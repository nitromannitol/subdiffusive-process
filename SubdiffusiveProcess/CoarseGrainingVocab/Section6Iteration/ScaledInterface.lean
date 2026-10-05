module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.Geometry
public import SubdiffusiveProcess.Section6.Defs.AffineMinimizers
public import SubdiffusiveProcess.Section6.Defs.Excess

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

open MeasureTheory
open Homogenization (axisCube)

noncomputable section

variable {d : ℕ}

/-! ### The `Affine`-indexed infimum is the engine's range-indexed one -/

/-- The competitor set of `excess` is the engine's `affineDistSet`. -/
theorem affineErrorSet_eq_affineDistSet (W : Set (Vec d)) (u : Vec d → ℝ) :
    {r : ℝ | ∃ ell : Affine d, r = affineError W u ell} = affineDistSet W u := by
  ext r
  constructor
  · rintro ⟨ell, rfl⟩
    exact ⟨(ell.constant, ell.slope), rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨⟨p.1, p.2⟩, rfl⟩

/-- The `excess` is the engine's scale-normalized excess. -/
theorem excess_eq_affineExcessScaled (j : ℤ) (W : Set (Vec d)) (u : Vec d → ℝ) :
    excess j W u = affineExcessScaled j W u := by
  rw [excess, affineExcessScaled, affineExcessRaw, affineErrorSet_eq_affineDistSet]

/-- The minimizer predicate is the engine's. -/
theorem mem_affineMinimizers_iff {W : Set (Vec d)} {u : Vec d → ℝ} {ell : Affine d} :
    ell ∈ affineMinimizers W u ↔ IsAffineMinimizer W u ell.constant ell.slope := by
  rw [IsAffineMinimizer, affineExcessRaw, ← affineErrorSet_eq_affineDistSet]
  exact Iff.rfl

/-- The slope magnitude is the engine's. -/
theorem sqrt_vecNormSq_eq_slopeMagnitude (g : Vec d) :
    Real.sqrt (Homogenization.vecNormSq g) = slopeMagnitude g := rfl

/-- The translate of the paper cube is the engine's translated open cube. -/
theorem translatedCube_eq (d : ℕ) (j : ℤ) (z : Vec d) :
    translatedCube d j z
      = (fun v => z + v) '' Homogenization.openCubeSet (Homogenization.originCube d j) := rfl

/-! ### The normalizer bridges for the excess -/

/-- The `3^{−j}`-normalized excess is below the `|W|^{−1/d}`-normalized one, on a
window sandwiched at aspect ratio `1/9`. -/
theorem affineExcessScaled_le_affineExcess_of_axisCubeSandwich (hd : d ≠ 0)
    {W : Set (Vec d)} {zin zout : Vec d} {j : ℤ}
    (hin : axisCube zin ((3 : ℝ) ^ (j - 2)) ⊆ W)
    (hout : W ⊆ axisCube zout ((3 : ℝ) ^ j)) (u : Vec d → ℝ) :
    affineExcessScaled j W u ≤ affineExcess W u := by
  obtain ⟨hlo, hhi⟩ := volume_toReal_bounds_of_axisCubeSandwich (d := d) hin hout
  obtain ⟨hlow, _⟩ := rpow_normalizer_bounds (d := d) hd hlo hhi
  exact mul_le_mul_of_nonneg_right hlow (affineExcessRaw_nonneg W u)

/-- The reverse normalizer comparison for the excess: the general normalizer costs
at most the factor `9`. -/
theorem affineExcess_le_affineExcessScaled_of_axisCubeSandwich (hd : d ≠ 0)
    {W : Set (Vec d)} {zin zout : Vec d} {j : ℤ}
    (hin : axisCube zin ((3 : ℝ) ^ (j - 2)) ⊆ W)
    (hout : W ⊆ axisCube zout ((3 : ℝ) ^ j)) (u : Vec d → ℝ) :
    affineExcess W u ≤ 9 * affineExcessScaled j W u := by
  obtain ⟨hlo, hhi⟩ := volume_toReal_bounds_of_axisCubeSandwich (d := d) hin hout
  obtain ⟨_, hhigh⟩ := rpow_normalizer_bounds (d := d) hd hlo hhi
  have h := mul_le_mul_of_nonneg_right hhigh (affineExcessRaw_nonneg W u)
  rw [affineExcess, affineExcessScaled]
  calc ((volume W).toReal) ^ (-(d : ℝ)⁻¹) * affineExcessRaw W u
      ≤ 9 * (3 : ℝ) ^ (-j) * affineExcessRaw W u := h
    _ = 9 * ((3 : ℝ) ^ (-j) * affineExcessRaw W u) := by ring

/-! ### The degenerate dimension `d = 0` -/

/-- In dimension zero the carrier is a singleton. -/
theorem vec_dim_zero_eq (x y : Vec 0) : x = y := funext fun i => i.elim0

/-- In dimension zero every function is constant, so on a window of positive
measure the volume average is that constant value. -/
theorem volumeAverage_dim_zero {W : Set (Vec 0)} (hW : 0 < (volume W).toReal)
    (f : Vec 0 → ℝ) (x0 : Vec 0) : Homogenization.volumeAverage W f = f x0 := by
  have hconst : f = fun _ : Vec 0 => f x0 := funext fun x => by rw [vec_dim_zero_eq x x0]
  have hint : ∫ x in W, f x ∂volume = (volume W).toReal • f x0 := by
    rw [hconst]
    exact setIntegral_const _
  rw [Homogenization.volumeAverage, hint, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (ne_of_gt hW), one_mul]

/-- In dimension zero the normalized seminorm on a window of positive measure is
the absolute value at the unique point. -/
theorem normalizedL2On_dim_zero {W : Set (Vec 0)} (hW : 0 < (volume W).toReal)
    (f : Vec 0 → ℝ) (x0 : Vec 0) : normalizedL2On W f = |f x0| := by
  rw [normalizedL2On, volumeAverage_dim_zero hW (fun x => f x ^ 2) x0,
    Real.sqrt_sq_eq_abs]

/-- In dimension zero the oscillation vanishes. -/
theorem normalizedL2On_sub_average_dim_zero {W : Set (Vec 0)}
    (hW : 0 < (volume W).toReal) (u : Vec 0 → ℝ) :
    normalizedL2On W (fun x => u x - averageOn W u) = 0 := by
  have hx0 : Vec 0 := fun i => i.elim0
  rw [normalizedL2On_dim_zero hW _ hx0, averageOn, volumeAverage_dim_zero hW u hx0,
    sub_self, abs_zero]

/-- In dimension zero the affine excess vanishes. -/
theorem excess_dim_zero {W : Set (Vec 0)} (hW : 0 < (volume W).toReal) (j : ℤ)
    (u : Vec 0 → ℝ) : excess j W u = 0 := by
  have hx0 : Vec 0 := fun i => i.elim0
  have hzero : affineDistOn W u (u hx0) 0 = 0 := by
    rw [affineDistOn, normalizedL2On_dim_zero hW _ hx0, affineEval]
    have hdot : Homogenization.vecDot (0 : Vec 0) hx0 = 0 := by
      simp [Homogenization.vecDot]
    rw [hdot, add_zero, sub_self, abs_zero]
  have hle : affineExcessRaw W u ≤ 0 := by
    have h := affineExcessRaw_le_affineDistOn W u (u hx0) 0
    rw [hzero] at h
    exact h
  have hge : 0 ≤ affineExcessRaw W u := affineExcessRaw_nonneg W u
  rw [excess_eq_affineExcessScaled, affineExcessScaled,
    le_antisymm hle hge, mul_zero]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
