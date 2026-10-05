module

public import SubdiffusiveProcess.Analysis.RadialTruncatedKernel
public import SubdiffusiveProcess.Analysis.CubeFractionalBounds
public import Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

open MeasureTheory Filter Set Homogenization
open scoped ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess

/-- The scalar Gagliardo integrand. -/
def cubeFractionalKernel {d : ℕ} (s : ℝ) (f : SpatialCoordinates d → ℝ)
    (x y : SpatialCoordinates d) : ℝ≥0∞ :=
  ENNReal.ofReal ((f x - f y) ^ 2) /
    ENNReal.ofReal (euclideanDist x y) ^ ((d : ℝ) + 2 * s)

theorem measurable_cubeFractionalKernel {d : ℕ} (s : ℝ)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f) :
    Measurable (fun p : SpatialCoordinates d × SpatialCoordinates d =>
      cubeFractionalKernel s f p.1 p.2) := by
  unfold cubeFractionalKernel euclideanDist euclideanNorm vecNormSq vecDot
  fun_prop

/-- Pointwise near/far decomposition, using the max-norm cutoff. -/
theorem cubeFractionalKernel_le_split {d : ℕ} (s t delta : ℝ) (ht : 0 < t)
    (hts : t < s) (_hdelta : 0 < delta) (f : SpatialCoordinates d → ℝ)
    (x y : SpatialCoordinates d) :
    cubeFractionalKernel t f x y ≤
      ENNReal.ofReal ((d : ℝ) * delta) ^ (2 * (s - t)) * cubeFractionalKernel s f x y +
        2 * (ENNReal.ofReal (f x ^ 2) + ENNReal.ofReal (f y ^ 2)) *
          cubeInterpolationKernel t delta (x - y) := by
  by_cases hxy : x = y
  · subst y
    simp only [cubeFractionalKernel, sub_self, zero_pow (by decide : 2 ≠ 0),
      ENNReal.ofReal_zero, ENNReal.zero_div, zero_le]
  have hdist0 : ENNReal.ofReal (euclideanDist x y) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (lt_of_le_of_ne (euclideanDist_nonneg x y)
      (Ne.symm ((euclideanDist_eq_zero_iff).not.mpr hxy)))
  have hq : 0 ≤ 2 * (s - t) := by linarith
  by_cases hnear : ‖x - y‖ ≤ delta
  · have hdistance : euclideanDist x y ≤ (d : ℝ) * delta :=
      (euclideanNorm_le_dimension_mul_norm (x - y)).trans
        (mul_le_mul_of_nonneg_left hnear (Nat.cast_nonneg d))
    have heq : ENNReal.ofReal (euclideanDist x y) ^ (-((d : ℝ) + 2 * t)) =
        ENNReal.ofReal (euclideanDist x y) ^ (2 * (s - t)) *
          ENNReal.ofReal (euclideanDist x y) ^ (-((d : ℝ) + 2 * s)) := by
      rw [← ENNReal.rpow_add _ _ hdist0 ENNReal.ofReal_ne_top]
      congr 1
      ring
    have hrewrite : cubeFractionalKernel t f x y =
        ENNReal.ofReal (euclideanDist x y) ^ (2 * (s - t)) * cubeFractionalKernel s f x y := by
      unfold cubeFractionalKernel
      rw [div_eq_mul_inv, ← ENNReal.rpow_neg, heq, div_eq_mul_inv, ← ENNReal.rpow_neg]
      ac_rfl
    rw [hrewrite]
    apply le_trans _ (le_add_of_nonneg_right zero_le)
    exact mul_le_mul_left (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hdistance) hq) _
  · have hfar : delta < ‖x - y‖ := lt_of_not_ge hnear
    have hnum : ENNReal.ofReal ((f x - f y) ^ 2) ≤
        2 * (ENNReal.ofReal (f x ^ 2) + ENNReal.ofReal (f y ^ 2)) := by
      calc
        _ ≤ ENNReal.ofReal (2 * (f x ^ 2 + f y ^ 2)) :=
          ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (f x + f y)])
        _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]; norm_num
    have hker : ENNReal.ofReal (euclideanDist x y) ^ (-((d : ℝ) + 2 * t)) ≤
        cubeInterpolationKernel t delta (x - y) := by
      unfold cubeInterpolationKernel
      rw [max_eq_right hfar.le]
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal (norm_le_euclideanNorm (x - y))) (by positivity))
    apply le_trans _ (le_add_of_nonneg_left zero_le)
    rw [cubeFractionalKernel, div_eq_mul_inv, ← ENNReal.rpow_neg]
    exact mul_le_mul hnum hker zero_le zero_le

/-- The two far-field terms are bounded by the kernel mass and the L2 square. -/
theorem double_lintegral_cubeInterpolationKernel_le {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t delta : ℝ) (hdelta : 0 < delta)
    (f : DomainL2 (centeredCube z r hr)) :
    (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        2 * (ENNReal.ofReal (f x ^ 2) + ENNReal.ofReal (f y ^ 2)) *
          cubeInterpolationKernel t delta (x - y)) ≤
      4 * (ENNReal.ofReal delta ^ (-(2 * t)) * cubeInterpolationKernelMass d t) *
        ENNReal.ofReal (‖f‖ ^ 2) := by
  let Q : Set (SpatialCoordinates d) := centeredCube z r hr
  let mu : Measure (SpatialCoordinates d) := volume.restrict Q
  let A : SpatialCoordinates d → ℝ≥0∞ := fun x => ENNReal.ofReal (f x ^ 2)
  let K : SpatialCoordinates d → SpatialCoordinates d → ℝ≥0∞ :=
    fun x y => cubeInterpolationKernel t delta (x - y)
  let M : ℝ≥0∞ := ENNReal.ofReal delta ^ (-(2 * t)) * cubeInterpolationKernelMass d t
  have hA : Measurable A := ((Lp.stronglyMeasurable f).measurable.pow_const 2).ennreal_ofReal
  have hK : Measurable (Function.uncurry K) :=
    (measurable_cubeInterpolationKernel t delta).comp (measurable_fst.sub measurable_snd)
  have h1 : Measurable (fun p : SpatialCoordinates d × SpatialCoordinates d => A p.1 * K p.1 p.2) :=
    (hA.comp measurable_fst).mul hK
  have h2 : Measurable (fun p : SpatialCoordinates d × SpatialCoordinates d => A p.2 * K p.1 p.2) :=
    (hA.comp measurable_snd).mul hK
  have hfar : Measurable (fun p : SpatialCoordinates d × SpatialCoordinates d =>
      2 * (A p.1 + A p.2) * K p.1 p.2) :=
    (measurable_const.mul ((hA.comp measurable_fst).add (hA.comp measurable_snd))).mul hK
  have hnorm : ENNReal.ofReal (‖f‖ ^ 2) = ∫⁻ x, A x ∂mu := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    exact eLpNorm_two_sq_eq_lintegral_sq_of_aestronglyMeasurable _ _ (Lp.aestronglyMeasurable f)
  have hfirst : (∫⁻ p, A p.1 * K p.1 p.2 ∂mu.prod mu) ≤ M * ENNReal.ofReal (‖f‖ ^ 2) := by
    rw [lintegral_prod _ h1.aemeasurable]
    calc
      (∫⁻ x, ∫⁻ y, A x * K x y ∂mu ∂mu) =
          ∫⁻ x, A x * ∫⁻ y, K x y ∂mu ∂mu := by
        apply lintegral_congr
        intro x
        exact lintegral_const_mul' (A x) _ ENNReal.ofReal_ne_top
      _ ≤ ∫⁻ x, A x * M ∂mu :=
        lintegral_mono (fun x => mul_le_mul_right
          (lintegral_cubeInterpolationKernel_sub_le t delta hdelta Q x) _)
      _ = (∫⁻ x, A x ∂mu) * M := lintegral_mul_const M hA
      _ = _ := by rw [← hnorm, mul_comm]
  have hsecond : (∫⁻ p, A p.2 * K p.1 p.2 ∂mu.prod mu) =
      ∫⁻ p, A p.1 * K p.1 p.2 ∂mu.prod mu := by
    rw [lintegral_prod _ h2.aemeasurable, lintegral_lintegral_swap h2.aemeasurable,
      lintegral_prod _ h1.aemeasurable]
    apply lintegral_congr
    intro y
    apply lintegral_congr
    intro x
    dsimp [K]
    rw [show cubeInterpolationKernel t delta (x - y) =
        cubeInterpolationKernel t delta (y - x) from by
      unfold cubeInterpolationKernel
      rw [norm_sub_rev]]
  calc
    (∫⁻ x in Q, ∫⁻ y in Q, 2 * (A x + A y) * K x y) =
        ∫⁻ p, 2 * (A p.1 * K p.1 p.2 + A p.2 * K p.1 p.2) ∂mu.prod mu := by
      rw [← lintegral_prod _ hfar.aemeasurable]
      apply lintegral_congr
      intro p
      ring
    _ = 2 * ((∫⁻ p, A p.1 * K p.1 p.2 ∂mu.prod mu) +
        ∫⁻ p, A p.2 * K p.1 p.2 ∂mu.prod mu) := by
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left h1]
    _ ≤ 2 * (M * ENNReal.ofReal (‖f‖ ^ 2) + M * ENNReal.ofReal (‖f‖ ^ 2)) := by
      rw [hsecond]
      exact mul_le_mul_right (add_le_add hfirst hfirst) _
    _ = _ := by ring

/-- Splitting the fractional integral at any positive scale. -/
theorem cubeGagliardoIntegral_le_split {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (s t delta : ℝ) (ht : 0 < t) (hts : t < s)
    (hdelta : 0 < delta) (f : DomainL2 (centeredCube z r hr)) :
    cubeGagliardoIntegral z r hr t f ≤
      ENNReal.ofReal ((d : ℝ) * delta) ^ (2 * (s - t)) * cubeGagliardoIntegral z r hr s f +
        4 * (ENNReal.ofReal delta ^ (-(2 * t)) * cubeInterpolationKernelMass d t) *
          ENNReal.ofReal (‖f‖ ^ 2) := by
  let Q : Set (SpatialCoordinates d) := centeredCube z r hr
  let mu : Measure (SpatialCoordinates d) := volume.restrict Q
  let A : ℝ≥0∞ := ENNReal.ofReal ((d : ℝ) * delta) ^ (2 * (s - t))
  have hf := (Lp.stronglyMeasurable f).measurable
  have hg (sigma : ℝ) : Measurable (fun p : SpatialCoordinates d × SpatialCoordinates d =>
      cubeFractionalKernel sigma f p.1 p.2) := measurable_cubeFractionalKernel sigma f hf
  have hprod (sigma : ℝ) : cubeGagliardoIntegral z r hr sigma f =
      ∫⁻ p, cubeFractionalKernel sigma f p.1 p.2 ∂mu.prod mu :=
    (lintegral_prod _ (hg sigma).aemeasurable).symm
  have hfar : Measurable (fun p : SpatialCoordinates d × SpatialCoordinates d =>
      2 * (ENNReal.ofReal (f p.1 ^ 2) + ENNReal.ofReal (f p.2 ^ 2)) *
        cubeInterpolationKernel t delta (p.1 - p.2)) := by
    have hk : Measurable (fun p : SpatialCoordinates d × SpatialCoordinates d =>
        cubeInterpolationKernel t delta (p.1 - p.2)) :=
      (measurable_cubeInterpolationKernel (d := d) t delta).comp
      (measurable_fst.sub measurable_snd)
    exact (measurable_const.mul (((hf.comp measurable_fst).pow_const 2).ennreal_ofReal.add
      ((hf.comp measurable_snd).pow_const 2).ennreal_ofReal)).mul hk
  calc
    cubeGagliardoIntegral z r hr t f =
        ∫⁻ p, cubeFractionalKernel t f p.1 p.2 ∂mu.prod mu := hprod t
    _ ≤ ∫⁻ p, A * cubeFractionalKernel s f p.1 p.2 +
        2 * (ENNReal.ofReal (f p.1 ^ 2) + ENNReal.ofReal (f p.2 ^ 2)) *
          cubeInterpolationKernel t delta (p.1 - p.2) ∂mu.prod mu :=
      lintegral_mono (fun p => cubeFractionalKernel_le_split s t delta ht hts hdelta f p.1 p.2)
    _ = A * cubeGagliardoIntegral z r hr s f +
        ∫⁻ p, 2 * (ENNReal.ofReal (f p.1 ^ 2) + ENNReal.ofReal (f p.2 ^ 2)) *
          cubeInterpolationKernel t delta (p.1 - p.2) ∂mu.prod mu := by
      rw [lintegral_add_left (show Measurable (fun p : SpatialCoordinates d × SpatialCoordinates d => A * cubeFractionalKernel s f p.1 p.2) from by simpa using! measurable_const.mul (hg s)), lintegral_const_mul A (hg s), ← hprod s]
    _ ≤ _ := by
      rw [lintegral_prod _ hfar.aemeasurable]
      exact add_le_add le_rfl (double_lintegral_cubeInterpolationKernel_le z r hr t delta hdelta f)

end SubdiffusiveProcess
