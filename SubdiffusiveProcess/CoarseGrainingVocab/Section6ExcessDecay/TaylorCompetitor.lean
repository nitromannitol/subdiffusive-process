module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows
public import Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry
public import Mathlib.Analysis.Calculus.MeanValue








@[expose] public section

/-!
# The affine (Taylor) competitor

Step 2 of the printed proof of `l.excess.decay.good.scales.GMC` converts a
gradient-Hölder bound on the harmonic replacement into excess decay:

```text
  E(v, U_{m,n-k}(x)) ≤ C 3^{(n-k)/2} [∇v]_{C^{0,1/2}} .
```

This module proves that conversion on an arbitrary truncated window and at the
frozen scale normalizer `3^{-j}`.  The competitor is the first-order Taylor
polynomial of the function at the window centre, built with the **average**
slope; the mean-value inequality prices its residual by `2 d K r^{3/2}` on a
window of sup-radius `r`.

The Hölder carrier of the section 6 frozen vocabulary is
`SubdiffusiveProcess.CoarseGrainingVocab.HolderSeminormBoundOn`, which is written against the
explicit Euclidean magnitude `Homogenization.euclideanNorm`, while the
mean-value inequality lives on the ambient sup norm of `Vec d`.  The two are
comparable at the dimensional factor `√d` (`Homogenization.norm_le_euclideanNorm`,
`Homogenization.euclideanNorm_le_dimension_mul_norm`), which is absorbed into
the constant.

## Scope

Deterministic support; nothing here knows about the model, the good event, or
harmonicity.

## References

* paper label `l.excess.decay.good.scales.GMC` (`step.l.excess.decay.good.scales.SubdiffusiveProcess.4`).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

open MeasureTheory
open Homogenization (vecDot volumeAverage volumeAverageVec euclideanNorm)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

variable {d : ℕ}

/-! ### The slope functional and the classical gradient carrier -/

/-- The continuous linear functional `v ↦ A · v` attached to a slope `A`. -/
def slopeCLM (A : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ i : Fin d, A i • ContinuousLinearMap.proj i

@[simp] theorem slopeCLM_apply (A v : Vec d) : slopeCLM A v = vecDot A v := by
  simp only [slopeCLM, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, vecDot]

theorem slopeCLM_sub (A B : Vec d) : slopeCLM A - slopeCLM B = slopeCLM (A - B) := by
  ext v
  simp only [sub_apply, slopeCLM_apply, vecDot, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The operator norm of the slope functional is at most `d ‖A‖`: the sup-norm
of `Vec d` dualizes to `ℓ¹`. -/
theorem norm_slopeCLM_le (A : Vec d) : ‖slopeCLM A‖ ≤ (d : ℝ) * ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Nat.cast_nonneg d) (norm_nonneg A)) fun v => ?_
  rw [slopeCLM_apply, Real.norm_eq_abs, vecDot]
  calc
    |∑ i : Fin d, A i * v i| ≤ ∑ i : Fin d, |A i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖A‖ * ‖v‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (by simpa using norm_le_pi_norm A i)
          (by simpa using norm_le_pi_norm v i) (abs_nonneg _) (norm_nonneg A)
    _ = (d : ℝ) * ‖A‖ * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem norm_slopeCLM_sub_le {G A : Vec d} {K : ℝ} (h : ‖G - A‖ ≤ K) :
    ‖slopeCLM G - slopeCLM A‖ ≤ (d : ℝ) * K := by
  rw [slopeCLM_sub]
  exact (norm_slopeCLM_le (G - A)).trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg d))

/-- **`f` is differentiable on `W` with gradient field `G`**: the classical `C¹`
half of the source hypothesis `h ∈ C^{1,1/2}`. -/
def HasGradientOn (W : Set (Vec d)) (f : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  ∀ y ∈ W, HasFDerivWithinAt f (slopeCLM (G y)) W y

theorem HasGradientOn.mono_set {U V : Set (Vec d)} {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hf : HasGradientOn U f G) (hVU : V ⊆ U) : HasGradientOn V f G :=
  fun y hy => (hf y (hVU hy)).mono hVU

/-! ### The affine lift -/

/-- **The affine lift** `ℓ(y) = c + A · (y - x)`: the affine function with slope
`A` taking the value `c` at `x`. -/
def affineLift (x : Vec d) (c : ℝ) (A : Vec d) : Vec d → ℝ :=
  fun y => c + vecDot A (y - x)

theorem vecDot_sub_right (A y x : Vec d) :
    vecDot A (y - x) = vecDot A y - vecDot A x := by
  simp only [vecDot, Pi.sub_apply]
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The affine lift is an affine competitor in the sense of the excess: it is
`affineEval` at intercept `c - A · x` and slope `A`. -/
theorem affineLift_eq_affineEval (x : Vec d) (c : ℝ) (A : Vec d) :
    affineLift x c A = affineEval (c - vecDot A x) A := by
  funext y
  rw [affineLift, affineEval, vecDot_sub_right]
  ring

/-! ### The mean-value residual -/

/-- **The affine-lift residual, at an arbitrary slope.**  If `f` is
differentiable on the convex window `W` with gradient field `G`, and `G` stays
within `K` of the slope `A` on `W`, then `f` differs from its affine lift at `x`
by at most `d K r` on a window of sup-radius `r` around `x`. -/
theorem abs_sub_affineLift_le {W : Set (Vec d)} {f : Vec d → ℝ} {G : Vec d → Vec d}
    {A : Vec d} {K r : ℝ} {x y : Vec d} (hW : Convex ℝ W) (hx : x ∈ W) (hy : y ∈ W)
    (hK : 0 ≤ K) (hf : HasGradientOn W f G) (hG : ∀ p ∈ W, ‖G p - A‖ ≤ K)
    (hr : ‖y - x‖ ≤ r) :
    |f y - affineLift x (f x) A y| ≤ (d : ℝ) * K * r := by
  have hmv : ‖f y - f x - slopeCLM A (y - x)‖ ≤ (d : ℝ) * K * ‖y - x‖ :=
    hW.norm_image_sub_le_of_norm_hasFDerivWithin_le' hf
      (fun p hp => norm_slopeCLM_sub_le (hG p hp)) hx hy
  have hdK : (0 : ℝ) ≤ (d : ℝ) * K := mul_nonneg (Nat.cast_nonneg d) hK
  have heq : f y - affineLift x (f x) A y = f y - f x - slopeCLM A (y - x) := by
    rw [affineLift, slopeCLM_apply]
    ring
  rw [heq, ← Real.norm_eq_abs]
  exact hmv.trans (mul_le_mul_of_nonneg_left hr hdK)

/-- **The average slope is an admissible base point.** -/
theorem norm_volumeAverageVec_sub_le {W : Set (Vec d)} {G : Vec d → Vec d}
    {A : Vec d} {K : ℝ} (hvolpos : 0 < volume W) (hvoltop : volume W < ⊤)
    (hint : ∀ i, IntegrableOn (fun y => G y i) W volume) (hK : 0 ≤ K)
    (hG : ∀ y ∈ W, ‖G y - A‖ ≤ K) :
    ‖volumeAverageVec W G - A‖ ≤ K := by
  have hvolreal : 0 < (volume W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hvolpos) (ne_of_lt hvoltop)
  refine (pi_norm_le_iff_of_nonneg hK).2 fun i => ?_
  have hIA : IntegrableOn (fun _ : Vec d => A i) W volume := by
    have : IsFiniteMeasure (volume.restrict W) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hvoltop⟩
    exact integrable_const _
  have hsplit : ∫ y in W, (G y i - A i) ∂volume =
      (∫ y in W, G y i ∂volume) - (volume W).toReal * A i := by
    rw [integral_sub (hint i) hIA, setIntegral_const, smul_eq_mul, measureReal_def]
  have hbound : ‖∫ y in W, (G y i - A i) ∂volume‖ ≤ K * (volume W).toReal := by
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := W)
      (f := fun y => G y i - A i) (C := K) hvoltop ?_
    · simpa [measureReal_def] using hb
    · intro y hy
      refine le_trans ?_ (hG y hy)
      simpa using norm_le_pi_norm (G y - A) i
  rw [hsplit] at hbound
  have hcoord : (volumeAverageVec W G - A) i =
      (volume W).toReal⁻¹ * ((∫ y in W, G y i ∂volume) - (volume W).toReal * A i) := by
    show volumeAverage W (fun y => G y i) - A i = _
    rw [volumeAverage]
    field_simp
  rw [hcoord, Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_of_lt (inv_pos.2 hvolreal))]
  rw [← Real.norm_eq_abs]
  calc
    (volume W).toReal⁻¹ * ‖(∫ y in W, G y i ∂volume) - (volume W).toReal * A i‖
        ≤ (volume W).toReal⁻¹ * (K * (volume W).toReal) :=
          mul_le_mul_of_nonneg_left hbound (le_of_lt (inv_pos.2 hvolreal))
    _ = K := by field_simp

private theorem rpow_half_mul_self {r : ℝ} (hr : 0 ≤ r) :
    r ^ (1 / 2 : ℝ) * r = r ^ (3 / 2 : ℝ) := by
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · rw [← hr0, Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num), mul_zero]
  · calc
      r ^ (1 / 2 : ℝ) * r = r ^ (1 / 2 : ℝ) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = r ^ ((1 / 2 : ℝ) + (1 : ℝ)) := (Real.rpow_add hrpos _ _).symm
      _ = r ^ (3 / 2 : ℝ) := by norm_num

/-- The frozen Euclidean Hölder carrier majorizes the sup-norm one at the
dimensional factor `√d`. -/
theorem norm_sub_le_of_holderSeminormBoundOn {W : Set (Vec d)} {G : Vec d → Vec d}
    {K r : ℝ} (hK : 0 ≤ K) (hr0 : 0 ≤ r)
    (hG : HolderSeminormBoundOn W (1 / 2 : ℝ) K G) {x : Vec d} (hx : x ∈ W)
    (hdiam : ∀ p ∈ W, ‖p - x‖ ≤ r) :
    ∀ p ∈ W, ‖G p - G x‖ ≤ K * Real.sqrt (d : ℝ) * r ^ (1 / 2 : ℝ) := by
  intro p hp
  have h1 : ‖G p - G x‖ ≤ euclideanNorm (G p - G x) :=
    Homogenization.norm_le_euclideanNorm _
  have h2 : euclideanNorm (G p - G x) ≤ K * euclideanNorm (p - x) ^ (1 / 2 : ℝ) :=
    hG p hp x hx
  have h3 : euclideanNorm (p - x) ≤ (d : ℝ) * r := by
    refine (Homogenization.euclideanNorm_le_dimension_mul_norm (p - x)).trans ?_
    exact mul_le_mul_of_nonneg_left (hdiam p hp) (Nat.cast_nonneg d)
  have h4 : euclideanNorm (p - x) ^ (1 / 2 : ℝ) ≤ ((d : ℝ) * r) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (le_trans (norm_nonneg _)
      (Homogenization.norm_le_euclideanNorm (p - x))) h3 (by norm_num)
  have h5 : ((d : ℝ) * r) ^ (1 / 2 : ℝ)
      = Real.sqrt (d : ℝ) * r ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (Nat.cast_nonneg d) hr0, Real.sqrt_eq_rpow]
  calc ‖G p - G x‖ ≤ K * euclideanNorm (p - x) ^ (1 / 2 : ℝ) := h1.trans h2
    _ ≤ K * (Real.sqrt (d : ℝ) * r ^ (1 / 2 : ℝ)) := by
        rw [← h5]; exact mul_le_mul_of_nonneg_left h4 hK
    _ = K * Real.sqrt (d : ℝ) * r ^ (1 / 2 : ℝ) := by ring

/-- **The residual bound.**  On a convex window `W` of sup-radius `r` around `x`,
with `f` of class `C^{1,1/2}` (gradient field `G`, frozen Hölder constant `K`),
the affine lift at the average slope satisfies
`|f(y) - ℓ(y)| ≤ 2 d √d K r^{3/2}` for every `y ∈ W`. -/
theorem abs_sub_affineLift_volumeAverage_le {W : Set (Vec d)} {f : Vec d → ℝ}
    {G : Vec d → Vec d} {K r : ℝ} {x y : Vec d} (hW : Convex ℝ W) (hx : x ∈ W)
    (hy : y ∈ W) (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hvolpos : 0 < volume W)
    (hvoltop : volume W < ⊤) (hint : ∀ i, IntegrableOn (fun p => G p i) W volume)
    (hf : HasGradientOn W f G) (hG : HolderSeminormBoundOn W (1 / 2 : ℝ) K G)
    (hdiam : ∀ p ∈ W, ‖p - x‖ ≤ r) :
    |f y - affineLift x (f x) (volumeAverageVec W G) y| ≤
      2 * (d : ℝ) * (K * Real.sqrt (d : ℝ)) * r ^ (3 / 2 : ℝ) := by
  set K' : ℝ := K * Real.sqrt (d : ℝ) with hK'def
  have hK' : 0 ≤ K' := mul_nonneg hK (Real.sqrt_nonneg _)
  have hK'r : 0 ≤ K' * r ^ (1 / 2 : ℝ) := mul_nonneg hK' (Real.rpow_nonneg hr0 _)
  have hbase : ∀ p ∈ W, ‖G p - G x‖ ≤ K' * r ^ (1 / 2 : ℝ) :=
    norm_sub_le_of_holderSeminormBoundOn hK hr0 hG hx hdiam
  have havg : ‖volumeAverageVec W G - G x‖ ≤ K' * r ^ (1 / 2 : ℝ) :=
    norm_volumeAverageVec_sub_le hvolpos hvoltop hint hK'r hbase
  have hslope : ∀ p ∈ W, ‖G p - volumeAverageVec W G‖ ≤ 2 * (K' * r ^ (1 / 2 : ℝ)) := by
    intro p hp
    have htri : ‖G p - volumeAverageVec W G‖ ≤
        ‖G p - G x‖ + ‖G x - volumeAverageVec W G‖ := by
      simpa using norm_sub_le_norm_sub_add_norm_sub (G p) (G x) (volumeAverageVec W G)
    rw [norm_sub_rev (G x)] at htri
    linarith only [htri, hbase p hp, havg]
  have hmain := abs_sub_affineLift_le (f := f) (G := G)
    (A := volumeAverageVec W G) hW hx hy
    (by linarith only [hK'r] : (0 : ℝ) ≤ 2 * (K' * r ^ (1 / 2 : ℝ))) hf hslope (hdiam y hy)
  refine hmain.trans (le_of_eq ?_)
  rw [← rpow_half_mul_self hr0]
  ring

/-! ### The excess form on a truncated window -/

/-- Points of a truncated window are within sup-distance `3^j/2` of its centre. -/
theorem norm_sub_le_of_mem_truncatedCube {x p : Vec d} {m j : ℤ}
    (hp : p ∈ truncatedCube d m j x) : ‖p - x‖ ≤ (3 : ℝ) ^ j / 2 := by
  have hpx : p - x ∈ cube d j := sub_mem_cube_of_mem_truncatedCube hp
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hpx
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have hi := hpx i
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith only [hi.1], by linarith only [hi.2]⟩

/-- The constant of the affine-competitor contraction: `2 d √d (1/2)^{3/2}`. -/
def taylorConst (d : ℕ) : ℝ := 2 * (d : ℝ) * Real.sqrt (d : ℝ) * ((1 : ℝ) / 2) ^ (3 / 2 : ℝ)

theorem taylorConst_nonneg (d : ℕ) : 0 ≤ taylorConst d := by
  rw [taylorConst]
  exact mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _)

/-- **The affine contraction.**  At the frozen scale normalizer,

```text
  excess j (U_{m,j}(x)) f ≤ C(d) · [∇f]_{C^{0,1/2}(U_{m,j}(x))} · (3^j)^{1/2} .
```

At `j = n - k` This is the printed `C 3^{(n-k)/2} [∇v]_{C^{0,1/2}}`. -/
theorem excess_le_taylor {m j : ℤ} {x : Vec d} (hx : x ∈ cube d m) (hjm : j - 1 ≤ m)
    {f : Vec d → ℝ} {G : Vec d → Vec d} {K : ℝ} (hK : 0 ≤ K)
    (hmem : MemLp f 2 (volume.restrict (truncatedCube d m j x)))
    (hint : ∀ i, IntegrableOn (fun p => G p i) (truncatedCube d m j x) volume)
    (hf : HasGradientOn (truncatedCube d m j x) f G)
    (hG : HolderSeminormBoundOn (truncatedCube d m j x) (1 / 2 : ℝ) K G) :
    excess j (truncatedCube d m j x) f ≤ taylorConst d * K * ((3 : ℝ) ^ j) ^ (1 / 2 : ℝ) := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  have hMnn : (0 : ℝ) ≤ 2 * (d : ℝ) * (K * Real.sqrt (d : ℝ)) * ((3 : ℝ) ^ j / 2) ^ (3 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hK (Real.sqrt_nonneg _)))
      (Real.rpow_nonneg (by positivity) _)
  have hxW : x ∈ truncatedCube d m j x := mem_truncatedCube_self j hx
  have hvolpos : 0 < volume (truncatedCube d m j x) := by
    have h := volume_toReal_truncatedCube_pos x hx hjm
    by_contra hcon
    rw [not_lt, nonpos_iff_eq_zero] at hcon
    rw [hcon] at h
    simp at h
  have hbound : ∀ p ∈ truncatedCube d m j x,
      |f p - affineEval (f x - vecDot (volumeAverageVec (truncatedCube d m j x) G) x)
          (volumeAverageVec (truncatedCube d m j x) G) p|
        ≤ 2 * (d : ℝ) * (K * Real.sqrt (d : ℝ)) * ((3 : ℝ) ^ j / 2) ^ (3 / 2 : ℝ) := by
    intro p hp
    have h := abs_sub_affineLift_volumeAverage_le (W := truncatedCube d m j x) (f := f)
      (G := G) (K := K) (r := (3 : ℝ) ^ j / 2) (x := x) (y := p)
      (convex_truncatedCube d m j x) hxW hp hK (by positivity) hvolpos
      (volume_truncatedCube_lt_top d m j x) hint hf hG
      (fun q hq => norm_sub_le_of_mem_truncatedCube hq)
    rwa [affineLift_eq_affineEval] at h
  have hraw : affineExcessRaw (truncatedCube d m j x) f
      ≤ 2 * (d : ℝ) * (K * Real.sqrt (d : ℝ)) * ((3 : ℝ) ^ j / 2) ^ (3 / 2 : ℝ) := by
    refine le_trans (affineExcessRaw_le_affineDistOn (truncatedCube d m j x) f
      (f x - vecDot (volumeAverageVec (truncatedCube d m j x) G) x)
      (volumeAverageVec (truncatedCube d m j x) G)) ?_
    rw [affineDistOn]
    exact normalizedL2On_le_of_abs_le (measurableSet_truncatedCube d m j x)
      (volume_toReal_truncatedCube_pos x hx hjm)
      (ne_of_lt (volume_truncatedCube_lt_top d m j x)) hMnn
      (integrableOn_sub_affineEval_sq_truncatedCube x hmem _ _) hbound
  have hsplit : ((3 : ℝ) ^ j / 2) ^ (3 / 2 : ℝ)
      = ((3 : ℝ) ^ j) ^ (3 / 2 : ℝ) * ((1 : ℝ) / 2) ^ (3 / 2 : ℝ) := by
    rw [show (3 : ℝ) ^ j / 2 = (3 : ℝ) ^ j * ((1 : ℝ) / 2) by ring,
      Real.mul_rpow hpos.le (by norm_num)]
  have hkey : (3 : ℝ) ^ (-j) * ((3 : ℝ) ^ j) ^ (3 / 2 : ℝ) = ((3 : ℝ) ^ j) ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_one,
      ← mul_assoc, zpow_neg, inv_mul_cancel₀ hpos.ne', one_mul]
  calc excess j (truncatedCube d m j x) f
      = (3 : ℝ) ^ (-j) * affineExcessRaw (truncatedCube d m j x) f := by
        rw [excess_eq_affineExcessScaled, affineExcessScaled]
    _ ≤ (3 : ℝ) ^ (-j) *
          (2 * (d : ℝ) * (K * Real.sqrt (d : ℝ)) * ((3 : ℝ) ^ j / 2) ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = taylorConst d * K * ((3 : ℝ) ^ j) ^ (1 / 2 : ℝ) := by
        rw [taylorConst, hsplit, ← hkey]
        ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
