module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows


-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/OneStepTriangle.lean

@[expose] public section

/-!
# The excess triangle inequality, the window transfer, and the slope split

Step 3 of the printed proof of `l.excess.decay.good.scales.GMC` is a chain of
four purely deterministic moves on the window family `U_{m,j}(x)`:

* **the excess triangle** `E(u,W) ≤ E(v,W) + 3^{-j}‖u-v‖_{L̲²(W)}`, proved
  competitor by competitor;
* **the window transfer** `‖u-v‖_{L̲²(U_{m,n-k})} ≤ C 3^{dk/2}‖u-v‖_{L̲²(U_{m,n-4})}`,
  the volume-ratio comparison of the family;
* **excess quasi-monotonicity** `E(u,U_{m,n-4}) ≤ C E(u,U_{m,n})`, at the frozen
  scale normalizer;
* **the slope split** `3^{-n}‖u-(u)_{U_{m,n}}‖ ≤ E(u,U_{m,n}) + C|∇ℓ|`, which is
  what converts the harmonic-approximation right-hand side into the excess and
  the best-affine slope of the printed estimate.

## Scope

Deterministic support.  Nothing here knows about the model, the good event, or
harmonicity.

## References
  (`step.l.excess.decay.good.scales.SubdiffusiveProcess.5`, `.6`).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

open MeasureTheory
open Homogenization (axisCube vecDot vecNormSq volumeAverage)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

variable {d : ℕ}

/-! ### Analytic slots on a truncated window -/

theorem memLp_affineEval_truncatedCube {m j : ℤ} (x : Vec d) (c : ℝ) (g : Vec d) :
    MemLp (affineEval c g) 2 (volume.restrict (truncatedCube d m j x)) := by
  refine memLp_affineEval_of_sandwich (zout := x + fun _ => -(1 / 2) * (3 : ℝ) ^ j)
    (Lout := (3 : ℝ) ^ j) (zpow_pos (by norm_num) j) (measurableSet_truncatedCube d m j x)
    ?_ c g
  refine subset_trans (truncatedCube_subset_translatedCube d m j x) ?_
  rw [translatedCube, cube, openCubeSet_originCube_eq_axisCube, image_add_axisCube]

theorem memLp_sub_affineEval_truncatedCube {m j : ℤ} (x : Vec d) {v : Vec d → ℝ}
    (hv : MemLp v 2 (volume.restrict (truncatedCube d m j x))) (c : ℝ) (g : Vec d) :
    MemLp (fun p => v p - affineEval c g p) 2
      (volume.restrict (truncatedCube d m j x)) :=
  hv.sub (memLp_affineEval_truncatedCube x c g)

theorem integrableOn_sub_const_sq_truncatedCube {m j : ℤ} (x : Vec d) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedCube d m j x))) (c : ℝ) :
    IntegrableOn (fun p => (u p - c) ^ 2) (truncatedCube d m j x) := by
  have h := integrableOn_sub_affineEval_sq_truncatedCube x hu c (0 : Vec d)
  have hfun : (fun p => (u p - affineEval c (0 : Vec d) p) ^ 2) = fun p => (u p - c) ^ 2 := by
    funext p
    simp only [affineEval]
    simp [vecDot]
  rwa [hfun] at h

theorem integrableOn_truncatedCube {m j : ℤ} (x : Vec d) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedCube d m j x))) :
    IntegrableOn u (truncatedCube d m j x) := by
  have : IsFiniteMeasure (volume.restrict (truncatedCube d m j x)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact volume_truncatedCube_lt_top d m j x
  exact hu.integrable one_le_two

/-! ### The excess triangle inequality -/

/-- **The triangle inequality for the unnormalized excess.**  Proved competitor
by competitor: the affine minimum of `u` is below every competitor of `v`,
displaced by the `L̲²` distance from `v` to `u`. -/
theorem affineExcessRaw_le_add {W : Set (Vec d)} {u v : Vec d → ℝ}
    (huv : MemLp (fun p => u p - v p) 2 (volume.restrict W))
    (hv : ∀ (c : ℝ) (g : Vec d),
      MemLp (fun p => v p - affineEval c g p) 2 (volume.restrict W)) :
    affineExcessRaw W u
      ≤ normalizedL2On W (fun p => u p - v p) + affineExcessRaw W v := by
  rw [← sub_le_iff_le_add']
  refine le_csInf (affineDistSet_nonempty W v) ?_
  rintro y ⟨q, rfl⟩
  rw [sub_le_iff_le_add']
  have hfun : (fun p => u p - affineEval q.1 q.2 p)
      = fun p => (u p - v p) + (v p - affineEval q.1 q.2 p) := by
    funext p; ring
  have hsplit := normalizedL2On_add_le (W := W) (f := fun p => u p - v p)
    (g := fun p => v p - affineEval q.1 q.2 p) huv (hv q.1 q.2)
  calc affineExcessRaw W u ≤ affineDistOn W u q.1 q.2 :=
        affineExcessRaw_le_affineDistOn W u q.1 q.2
    _ = normalizedL2On W (fun p => (u p - v p) + (v p - affineEval q.1 q.2 p)) := by
        rw [affineDistOn, hfun]
    _ ≤ normalizedL2On W (fun p => u p - v p) + affineDistOn W v q.1 q.2 := hsplit

/-- **The excess triangle inequality at the frozen scale normalizer.** -/
theorem excess_le_add {W : Set (Vec d)} (j : ℤ) {u v : Vec d → ℝ}
    (huv : MemLp (fun p => u p - v p) 2 (volume.restrict W))
    (hv : ∀ (c : ℝ) (g : Vec d),
      MemLp (fun p => v p - affineEval c g p) 2 (volume.restrict W)) :
    excess j W u ≤ excess j W v + (3 : ℝ) ^ (-j) * normalizedL2On W (fun p => u p - v p) := by
  have h := affineExcessRaw_le_add huv hv
  have hmul := mul_le_mul_of_nonneg_left h
    (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 3) (-j)))
  rw [excess_eq_affineExcessScaled, excess_eq_affineExcessScaled, affineExcessScaled,
    affineExcessScaled]
  linarith only [hmul]

/-! ### The window transfer -/

/-- **The window transfer.**  Passing from `U_{m,l}(x)` to the smaller
`U_{m,j}(x)` costs the square root of the explicit volume ratio. -/
theorem normalizedL2On_truncatedCube_le {m j l : ℤ} {x : Vec d} (hx : x ∈ cube d m)
    (hjm : j - 1 ≤ m) (hlm : l - 1 ≤ m) (hjl : j ≤ l) {f : Vec d → ℝ}
    (hint : IntegrableOn (fun p => f p ^ 2) (truncatedCube d m l x)) :
    normalizedL2On (truncatedCube d m j x) f
      ≤ Real.sqrt (((3 : ℝ) ^ (l - j + 2)) ^ d) * normalizedL2On (truncatedCube d m l x) f := by
  have hsub : truncatedCube d m j x ⊆ truncatedCube d m l x := truncatedCube_mono d m x hjl
  have hW : 0 < (volume (truncatedCube d m l x)).toReal :=
    volume_toReal_truncatedCube_pos x hx hlm
  have hW' : 0 < (volume (truncatedCube d m j x)).toReal :=
    volume_toReal_truncatedCube_pos x hx hjm
  refine (normalizedL2On_le_of_subset hsub hW hW' hint).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (normalizedL2On_nonneg _ _)
  exact Real.sqrt_le_sqrt (volume_ratio_truncatedCube_le x hx hjm hlm)

/-! ### Excess quasi-monotonicity at the scale normalizer -/

/-- **Excess quasi-monotonicity on the one-step family**, at the frozen scale
normalizer and the explicit ratio constant. -/
theorem excess_truncatedCube_le {m j l : ℤ} {x : Vec d} (hx : x ∈ cube d m)
    (hjm : j - 1 ≤ m) (hlm : l - 1 ≤ m) (hjl : j ≤ l) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedCube d m l x))) :
    excess j (truncatedCube d m j x) u
      ≤ (3 : ℝ) ^ (l - j) * Real.sqrt (((3 : ℝ) ^ (l - j + 2)) ^ d) *
          excess l (truncatedCube d m l x) u := by
  have hsub : truncatedCube d m j x ⊆ truncatedCube d m l x := truncatedCube_mono d m x hjl
  have hW : 0 < (volume (truncatedCube d m l x)).toReal :=
    volume_toReal_truncatedCube_pos x hx hlm
  have hW' : 0 < (volume (truncatedCube d m j x)).toReal :=
    volume_toReal_truncatedCube_pos x hx hjm
  have hraw := affineExcessRaw_le_of_subset (u := u) hsub hW hW'
    (integrableOn_sub_affineEval_sq_truncatedCube x hu)
  have hratio : Real.sqrt ((volume (truncatedCube d m l x)).toReal /
        (volume (truncatedCube d m j x)).toReal)
      ≤ Real.sqrt (((3 : ℝ) ^ (l - j + 2)) ^ d) :=
    Real.sqrt_le_sqrt (volume_ratio_truncatedCube_le x hx hjm hlm)
  have hchain : affineExcessRaw (truncatedCube d m j x) u
      ≤ Real.sqrt (((3 : ℝ) ^ (l - j + 2)) ^ d) *
          affineExcessRaw (truncatedCube d m l x) u :=
    hraw.trans (mul_le_mul_of_nonneg_right hratio (affineExcessRaw_nonneg _ _))
  have hzpow : (3 : ℝ) ^ (-j) = (3 : ℝ) ^ (l - j) * (3 : ℝ) ^ (-l) := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring_nf
  rw [excess_eq_affineExcessScaled, excess_eq_affineExcessScaled, affineExcessScaled,
    affineExcessScaled, hzpow]
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (l - j) * (3 : ℝ) ^ (-l) := by positivity
  calc (3 : ℝ) ^ (l - j) * (3 : ℝ) ^ (-l) * affineExcessRaw (truncatedCube d m j x) u
      ≤ (3 : ℝ) ^ (l - j) * (3 : ℝ) ^ (-l) *
          (Real.sqrt (((3 : ℝ) ^ (l - j + 2)) ^ d) *
            affineExcessRaw (truncatedCube d m l x) u) :=
        mul_le_mul_of_nonneg_left hchain hpos.le
    _ = (3 : ℝ) ^ (l - j) * Real.sqrt (((3 : ℝ) ^ (l - j + 2)) ^ d) *
          ((3 : ℝ) ^ (-l) * affineExcessRaw (truncatedCube d m l x) u) := by ring

/-! ### The slope split -/

/-- The Euclidean magnitude of a displacement inside a truncated window. -/
theorem slopeMagnitude_sub_le_of_mem_truncatedCube {x p : Vec d} {m j : ℤ}
    (hp : p ∈ truncatedCube d m j x) :
    slopeMagnitude (p - x) ≤ Real.sqrt (d : ℝ) * ((3 : ℝ) ^ j / 2) := by
  have hcoord : ∀ i : Fin d, ((p - x) i) ^ 2 ≤ ((3 : ℝ) ^ j / 2) ^ 2 := by
    intro i
    have hpx : p - x ∈ cube d j := sub_mem_cube_of_mem_truncatedCube hp
    rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hpx
    have hi := hpx i
    have habs : |(p - x) i| ≤ (3 : ℝ) ^ j / 2 := by
      rw [abs_le]
      exact ⟨by linarith only [hi.1], by linarith only [hi.2]⟩
    calc ((p - x) i) ^ 2 = |(p - x) i| ^ 2 := (sq_abs _).symm
      _ ≤ ((3 : ℝ) ^ j / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hsum : vecNormSq (p - x) ≤ (d : ℝ) * ((3 : ℝ) ^ j / 2) ^ 2 := by
    rw [vecNormSq, vecDot]
    calc ∑ i : Fin d, (p - x) i * (p - x) i
        ≤ ∑ _i : Fin d, ((3 : ℝ) ^ j / 2) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← pow_two]
          exact hcoord i
      _ = (d : ℝ) * ((3 : ℝ) ^ j / 2) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hj : (0 : ℝ) ≤ (3 : ℝ) ^ j / 2 := by positivity
  calc slopeMagnitude (p - x) = Real.sqrt (vecNormSq (p - x)) := rfl
    _ ≤ Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ j / 2) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * ((3 : ℝ) ^ j / 2) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hj]

/-- An affine function varies by at most `√d |∇ℓ| 3^j/2` across a truncated
window. -/
theorem abs_affine_sub_le_of_mem_truncatedCube {m j : ℤ} {x : Vec d} (ell : Affine d)
    {p : Vec d} (hp : p ∈ truncatedCube d m j x) :
    |ell.eval p - ell.eval x| ≤
      Real.sqrt (d : ℝ) * ((3 : ℝ) ^ j / 2) * slopeMagnitude ell.slope := by
  have hdot : ell.eval p - ell.eval x = vecDot ell.slope (p - x) := by
    rw [Affine.eval, Affine.eval, vecDot, vecDot, vecDot]
    simp only [Pi.sub_apply, mul_sub]
    rw [Finset.sum_sub_distrib]
    ring
  rw [hdot]
  refine (abs_vecDot_le_slopeMagnitude_mul ell.slope (p - x)).trans ?_
  rw [mul_comm (slopeMagnitude ell.slope)]
  exact mul_le_mul_of_nonneg_right (slopeMagnitude_sub_le_of_mem_truncatedCube hp)
    (slopeMagnitude_nonneg _)

/-- The frozen affine minimizers attain the unnormalized excess. -/
theorem affineError_eq_affineExcessRaw {W : Set (Vec d)} {u : Vec d → ℝ} {ell : Affine d}
    (hell : ell ∈ affineMinimizers W u) : affineError W u ell = affineExcessRaw W u := by
  rw [affineMinimizers, Set.mem_ofPred_eq, affineErrorSet_eq_affineDistSet] at hell
  exact hell

/-- **The slope split.**  The normalized oscillation of `u` on `U_{m,n}(x)` is
controlled by its excess and the magnitude of the best-affine slope:

```text
  3^{-n} ‖u - (u)_{U_{m,n}(x)}‖_{L̲²} ≤ E(u,U_{m,n}(x)) + (√d/2) |∇ℓ| .
```
-/
theorem normalizedL2On_sub_average_le {m n : ℤ} {x : Vec d} (hx : x ∈ cube d m)
    (hnm : n - 1 ≤ m) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedCube d m n x))) {ell : Affine d}
    (hell : ell ∈ affineMinimizers (truncatedCube d m n x) u) :
    (3 : ℝ) ^ (-n) * normalizedL2On (truncatedCube d m n x)
        (fun q => u q - averageOn (truncatedCube d m n x) u)
      ≤ excess n (truncatedCube d m n x) u +
          Real.sqrt (d : ℝ) / 2 * Real.sqrt (vecNormSq ell.slope) := by
  set W := truncatedCube d m n x with hWdef
  have hWm : MeasurableSet W := measurableSet_truncatedCube d m n x
  have hWpos : 0 < (volume W).toReal := volume_toReal_truncatedCube_pos x hx hnm
  have hWfin : volume W ≠ ⊤ := ne_of_lt (volume_truncatedCube_lt_top d m n x)
  -- the mean minimizes the deviation among constants
  have hmean : normalizedL2On W (fun q => u q - volumeAverage W u)
      ≤ normalizedL2On W (fun q => u q - ell.eval x) :=
    normalizedL2On_sub_volumeAverage_le hWm hWpos hWfin (integrableOn_truncatedCube x hu)
      (integrableOn_sub_affineEval_sq_truncatedCube x hu 0 0 |>.congr_fun
        (fun q => by simp only [affineEval]; simp [vecDot]) hWm) (ell.eval x)
  -- split the constant competitor into the minimizer plus an affine oscillation
  have hfun : (fun q => u q - ell.eval x)
      = fun q => (u q - ell.eval q) + (ell.eval q - ell.eval x) := by
    funext q; ring
  have hmemA : MemLp (fun q => u q - ell.eval q) 2 (volume.restrict W) := by
    have h := memLp_sub_affineEval_truncatedCube (m := m) (j := n) x hu ell.constant ell.slope
    exact h
  have hmemB : MemLp (fun q => ell.eval q - ell.eval x) 2 (volume.restrict W) := by
    have h1 : MemLp (affineEval ell.constant ell.slope) 2 (volume.restrict W) :=
      memLp_affineEval_truncatedCube x ell.constant ell.slope
    have : IsFiniteMeasure (volume.restrict W) := by
      constructor
      rw [Measure.restrict_apply_univ]
      exact volume_truncatedCube_lt_top d m n x
    exact h1.sub (memLp_const _)
  have hsplit := normalizedL2On_add_le (W := W) (f := fun q => u q - ell.eval q)
    (g := fun q => ell.eval q - ell.eval x) hmemA hmemB
  -- the affine oscillation is at most √d |∇ℓ| 3ⁿ/2
  have hosc : normalizedL2On W (fun q => ell.eval q - ell.eval x)
      ≤ Real.sqrt (d : ℝ) * ((3 : ℝ) ^ n / 2) * slopeMagnitude ell.slope := by
    refine normalizedL2On_le_of_abs_le hWm hWpos hWfin
      (mul_nonneg (by positivity) (slopeMagnitude_nonneg _)) ?_
      (fun q hq => abs_affine_sub_le_of_mem_truncatedCube ell hq)
    have h1 : IntegrableOn (fun q => (ell.eval q - ell.eval x) ^ 2) W := by
      have h2 := integrableOn_sub_affineEval_sq_truncatedCube (m := m) (j := n) x
        (u := fun q => ell.eval q) ?_ (ell.eval x) 0
      · refine h2.congr_fun (fun q => ?_) hWm
        simp only [affineEval]
        simp [vecDot]
      · exact memLp_affineEval_truncatedCube x ell.constant ell.slope
    exact h1
  -- the minimizer's error is the unnormalized excess
  have hmin : normalizedL2On W (fun q => u q - ell.eval q) = affineExcessRaw W u := by
    rw [← affineError_eq_affineExcessRaw hell, affineError]
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ (-n) := zpow_pos (by norm_num) _
  have hchain : normalizedL2On W (fun q => u q - volumeAverage W u)
      ≤ affineExcessRaw W u + Real.sqrt (d : ℝ) * ((3 : ℝ) ^ n / 2) * slopeMagnitude ell.slope := by
    rw [hfun] at hmean
    rw [← hmin]
    linarith only [hmean, hsplit, hosc]
  have hmul := mul_le_mul_of_nonneg_left hchain h3pos.le
  have hcancel : (3 : ℝ) ^ (-n) * (Real.sqrt (d : ℝ) * ((3 : ℝ) ^ n / 2))
      = Real.sqrt (d : ℝ) / 2 := by
    rw [zpow_neg]
    field_simp
  rw [averageOn, excess_eq_affineExcessScaled, affineExcessScaled]
  calc (3 : ℝ) ^ (-n) * normalizedL2On W (fun q => u q - volumeAverage W u)
      ≤ (3 : ℝ) ^ (-n) * (affineExcessRaw W u +
          Real.sqrt (d : ℝ) * ((3 : ℝ) ^ n / 2) * slopeMagnitude ell.slope) := hmul
    _ = (3 : ℝ) ^ (-n) * affineExcessRaw W u +
          Real.sqrt (d : ℝ) / 2 * slopeMagnitude ell.slope := by
        rw [mul_add, ← mul_assoc, hcancel]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
