module

public import SubdiffusiveProcess.Analysis.FractionalCutoffKernel
public import SubdiffusiveProcess.Analysis.CubeFractionalSplit

@[expose] public section

open MeasureTheory Set Homogenization _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess

/-- Cut off a function defined on a larger cube. -/
def fractionalCutoffExtension {d : ℕ} (U : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) : ℝ :=
  cubeExtensionCutoff x * U.indicator f x

/-- The local fractional kernel after multiplication by the cutoff. -/
theorem cubeFractionalKernel_mul_cutoff_le {d : ℕ} (s : ℝ)
    (f : SpatialCoordinates d → ℝ) (x y : SpatialCoordinates d) :
    cubeFractionalKernel s (fun a => cubeExtensionCutoff a * f a) x y ≤
      2 * cubeFractionalKernel s f x y +
        2 * ENNReal.ofReal (f y ^ 2) *
          cubeFractionalKernel s cubeExtensionCutoff x y := by
  have hc : (cubeExtensionCutoff x) ^ 2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ (cubeExtensionCutoff_nonneg x) zero_le_one).mpr
      (cubeExtensionCutoff_le_one x)
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (f x - f y))
  have hnum : (cubeExtensionCutoff x * f x - cubeExtensionCutoff y * f y) ^ 2 ≤
      2 * (f x - f y) ^ 2 + 2 * (f y) ^ 2 * (cubeExtensionCutoff x - cubeExtensionCutoff y) ^ 2 := by
    nlinarith [sq_nonneg (cubeExtensionCutoff x * (f x - f y) -
      (cubeExtensionCutoff x - cubeExtensionCutoff y) * f y)]
  have hnumE : ENNReal.ofReal ((cubeExtensionCutoff x * f x - cubeExtensionCutoff y * f y) ^ 2) ≤
      2 * ENNReal.ofReal ((f x - f y) ^ 2) +
        2 * ENNReal.ofReal (f y ^ 2) * ENNReal.ofReal ((cubeExtensionCutoff x - cubeExtensionCutoff y) ^ 2) := by
    have h := ENNReal.ofReal_le_ofReal hnum
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * f y ^ 2),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
    norm_num only [ENNReal.ofReal_ofNat] at h
    exact h
  unfold cubeFractionalKernel
  calc
    _ ≤ (2 * ENNReal.ofReal ((f x - f y) ^ 2) +
        2 * ENNReal.ofReal (f y ^ 2) * ENNReal.ofReal ((cubeExtensionCutoff x - cubeExtensionCutoff y) ^ 2)) /
          ENNReal.ofReal (euclideanDist x y) ^ ((d : ℝ) + 2 * s) :=
      ENNReal.div_le_div_right hnumE _
    _ = _ := by simp only [div_eq_mul_inv]; ring

/-- The global kernel is bounded by an interior term and a radial cutoff error. -/
theorem cubeFractionalKernel_cutoffExtension_le {d : ℕ} (s : ℝ) (hs : 0 ≤ s)
    (U : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ)
    (hU : ∀ x, x ∉ U → cubeExtensionCutoff x = 0) (x y : SpatialCoordinates d) :
    cubeFractionalKernel s (fractionalCutoffExtension U f) x y ≤
      2 * (if x ∈ U ∧ y ∈ U then cubeFractionalKernel s f x y else 0) +
        2 * (ENNReal.ofReal ((U.indicator f x) ^ 2) +
          ENNReal.ofReal ((U.indicator f y) ^ 2)) * fractionalCutoffKernel s (x - y) := by
  classical
  let g : SpatialCoordinates d → ℝ := U.indicator f
  by_cases hboth : x ∈ U ∧ y ∈ U
  · have hm := cubeFractionalKernel_mul_cutoff_le s f x y
    have heq : cubeFractionalKernel s (fractionalCutoffExtension U f) x y =
        cubeFractionalKernel s (fun a => cubeExtensionCutoff a * f a) x y := by
      simp only [cubeFractionalKernel, fractionalCutoffExtension,
        Set.indicator_of_mem hboth.1, Set.indicator_of_mem hboth.2]
    rw [heq, ite_eq_left hboth]
    apply hm.trans
    apply add_le_add le_rfl
    have herr := cubeExtensionCutoff_kernel_le s hs x y
    have hA : ENNReal.ofReal (f y ^ 2) ≤
        ENNReal.ofReal ((U.indicator f x) ^ 2) + ENNReal.ofReal ((U.indicator f y) ^ 2) := by
      simp only [Set.indicator_of_mem hboth.1, Set.indicator_of_mem hboth.2]
      exact le_add_of_nonneg_left zero_le
    change 2 * ENNReal.ofReal (f y ^ 2) * cubeFractionalKernel s cubeExtensionCutoff x y ≤ _
    exact mul_le_mul (mul_le_mul_of_nonneg_left hA zero_le) herr zero_le zero_le
  · have hnum : (fractionalCutoffExtension U f x - fractionalCutoffExtension U f y) ^ 2 =
        (g x ^ 2 + g y ^ 2) * (cubeExtensionCutoff x - cubeExtensionCutoff y) ^ 2 := by
      by_cases hx : x ∈ U
      · have hy : y ∉ U := fun hy => hboth ⟨hx, hy⟩
        simp only [fractionalCutoffExtension, g, Set.indicator_of_notMem hy, hU y hy,
          mul_zero, sub_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
        ring
      · simp only [fractionalCutoffExtension, g, Set.indicator_of_notMem hx, hU x hx,
          mul_zero, zero_sub, zero_pow (by decide : 2 ≠ 0), zero_add]
        ring
    have heq : cubeFractionalKernel s (fractionalCutoffExtension U f) x y =
        (ENNReal.ofReal (g x ^ 2) + ENNReal.ofReal (g y ^ 2)) *
          cubeFractionalKernel s cubeExtensionCutoff x y := by
      unfold cubeFractionalKernel
      rw [hnum, ENNReal.ofReal_mul (by positivity : 0 ≤ g x ^ 2 + g y ^ 2),
        ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      simp only [div_eq_mul_inv]
      ring
    rw [heq, ite_eq_right hboth, mul_zero, zero_add]
    calc
      _ ≤ (ENNReal.ofReal (g x ^ 2) + ENNReal.ofReal (g y ^ 2)) *
          fractionalCutoffKernel s (x - y) :=
        mul_le_mul_of_nonneg_left (cubeExtensionCutoff_kernel_le s hs x y) zero_le
      _ ≤ _ := by
        have h : (ENNReal.ofReal (g x ^ 2) + ENNReal.ofReal (g y ^ 2)) * fractionalCutoffKernel s (x - y) ≤
            (ENNReal.ofReal (g x ^ 2) + ENNReal.ofReal (g y ^ 2)) * fractionalCutoffKernel s (x - y) +
              (ENNReal.ofReal (g x ^ 2) + ENNReal.ofReal (g y ^ 2)) * fractionalCutoffKernel s (x - y) :=
          le_add_of_nonneg_right zero_le
        simpa only [g, two_mul, add_mul] using! h

/-- Integration of the two radial error terms uses only their mass and the L2 integral. -/
theorem double_lintegral_fractionalCutoffKernel {d : ℕ} (s : ℝ)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g) :
    (∫⁻ x : SpatialCoordinates d, ∫⁻ y : SpatialCoordinates d,
      2 * (ENNReal.ofReal (g x ^ 2) + ENNReal.ofReal (g y ^ 2)) *
        fractionalCutoffKernel s (x - y)) =
      4 * fractionalCutoffKernelMass d s * ∫⁻ x : SpatialCoordinates d, ENNReal.ofReal (g x ^ 2) := by
  let A : SpatialCoordinates d → ℝ≥0∞ := fun x => ENNReal.ofReal (g x ^ 2)
  let K : SpatialCoordinates d → SpatialCoordinates d → ℝ≥0∞ := fun x y => fractionalCutoffKernel s (x - y)
  let M : ℝ≥0∞ := fractionalCutoffKernelMass d s
  let I : ℝ≥0∞ := ∫⁻ x : SpatialCoordinates d, A x
  have hA : Measurable A := (hg.pow_const 2).ennreal_ofReal
  have hK : Measurable (Function.uncurry K) :=
    (measurable_fractionalCutoffKernel s).comp (measurable_fst.sub measurable_snd)
  have h1 : Measurable (fun p : SpatialCoordinates d × SpatialCoordinates d => A p.1 * K p.1 p.2) :=
    (hA.comp measurable_fst).mul hK
  have h2 : Measurable (fun p : SpatialCoordinates d × SpatialCoordinates d => A p.2 * K p.1 p.2) :=
    (hA.comp measurable_snd).mul hK
  have hR : Measurable (fun p : SpatialCoordinates d × SpatialCoordinates d => 2 * (A p.1 + A p.2) * K p.1 p.2) :=
    (measurable_const.mul ((hA.comp measurable_fst).add (hA.comp measurable_snd))).mul hK
  have hfirst : (∫⁻ p : SpatialCoordinates d × SpatialCoordinates d,
      A p.1 * K p.1 p.2 ∂volume.prod volume) = M * I := by
    rw [lintegral_prod _ h1.aemeasurable]
    calc
      _ = ∫⁻ x : SpatialCoordinates d, A x * M := by
        apply lintegral_congr
        intro x
        change (∫⁻ y : SpatialCoordinates d, A x * K x y) = A x * M
        rw [lintegral_const_mul' (A x) _ (show A x ≠ ⊤ from ENNReal.ofReal_ne_top)]
        rw [lintegral_fractionalCutoffKernel_sub]
      _ = _ := by rw [lintegral_mul_const M hA, mul_comm]
  have hsecond : (∫⁻ p : SpatialCoordinates d × SpatialCoordinates d,
      A p.2 * K p.1 p.2 ∂volume.prod volume) = M * I := by
    rw [lintegral_prod _ h2.aemeasurable, lintegral_lintegral_swap h2.aemeasurable]
    convert hfirst using 1
    rw [lintegral_prod _ h1.aemeasurable]
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro y
    dsimp [K]
    rw [fractionalCutoffKernel_sub_rev]
  calc
    _ = ∫⁻ p : SpatialCoordinates d × SpatialCoordinates d,
        2 * (A p.1 * K p.1 p.2 + A p.2 * K p.1 p.2) ∂volume.prod volume := by
      rw [← lintegral_prod _ hR.aemeasurable]
      apply lintegral_congr
      intro p
      ring
    _ = 2 * ((∫⁻ p : SpatialCoordinates d × SpatialCoordinates d,
        A p.1 * K p.1 p.2 ∂volume.prod volume) + ∫⁻ p : SpatialCoordinates d × SpatialCoordinates d,
        A p.2 * K p.1 p.2 ∂volume.prod volume) := by
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left h1]
    _ = _ := by rw [hfirst, hsecond]; ring

/-- A global cutoff estimate on any measurable set containing the support of the cutoff. -/
theorem globalFractionalSqNorm_cutoffExtension_le {d : ℕ} (s : ℝ) (hs : 0 ≤ s)
    (U : Set (SpatialCoordinates d)) (hUm : MeasurableSet U)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f)
    (hU : ∀ x, x ∉ U → cubeExtensionCutoff x = 0) :
    globalFractionalSqNorm s (fractionalCutoffExtension U f) ≤
      2 * (∫⁻ x in U, ∫⁻ y in U, cubeFractionalKernel s f x y) +
        (1 + 4 * fractionalCutoffKernelMass d s) * ∫⁻ x in U, ENNReal.ofReal (f x ^ 2) := by
  classical
  let g : SpatialCoordinates d → ℝ := U.indicator f
  let V : SpatialCoordinates d → ℝ := fractionalCutoffExtension U f
  let I : ℝ≥0∞ := ∫⁻ x in U, ENNReal.ofReal (f x ^ 2)
  let D : ℝ≥0∞ := ∫⁻ x in U, ∫⁻ y in U, cubeFractionalKernel s f x y
  let H : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun p =>
    if p.1 ∈ U ∧ p.2 ∈ U then cubeFractionalKernel s f p.1 p.2 else 0
  let R : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun p =>
    2 * (ENNReal.ofReal (g p.1 ^ 2) + ENNReal.ofReal (g p.2 ^ 2)) *
      fractionalCutoffKernel s (p.1 - p.2)
  have hg : Measurable g := hf.indicator hUm
  have hV : Measurable V := (cubeExtensionCutoff_lipschitz.continuous.measurable).mul hg
  have hH : Measurable H := Measurable.ite
    ((hUm.preimage measurable_fst).inter (hUm.preimage measurable_snd))
    (measurable_cubeFractionalKernel s f hf) measurable_const
  have hR : Measurable R := by
    change Measurable ((fun p : SpatialCoordinates d × SpatialCoordinates d => 2 * (ENNReal.ofReal (g p.1 ^ 2) + ENNReal.ofReal (g p.2 ^ 2))) * (fun p => fractionalCutoffKernel s (p.1 - p.2)))
    apply Measurable.mul
    · exact measurable_const.mul
        (((hg.comp measurable_fst).pow_const 2).ennreal_ofReal.add
          ((hg.comp measurable_snd).pow_const 2).ennreal_ofReal)
    · exact (measurable_fractionalCutoffKernel s).comp (measurable_fst.sub measurable_snd)
  have hI : (∫⁻ x : SpatialCoordinates d, ENNReal.ofReal (g x ^ 2)) = I := by
    rw [show I = ∫⁻ x : SpatialCoordinates d,
      U.indicator (fun x => ENNReal.ofReal (f x ^ 2)) x from (lintegral_indicator hUm _).symm]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ U
    · simp only [g, Set.indicator_of_mem hx]
    · simp only [g, Set.indicator_of_notMem hx, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero]
  have hL : (∫⁻ x : SpatialCoordinates d, ENNReal.ofReal (V x ^ 2)) ≤ I := by
    rw [← hI]
    apply lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    have hc : cubeExtensionCutoff x ^ 2 ≤ 1 := by
      simpa only [one_pow] using (sq_le_sq₀ (cubeExtensionCutoff_nonneg x) zero_le_one).mpr
        (cubeExtensionCutoff_le_one x)
    simpa only [V, fractionalCutoffExtension, g, mul_pow, one_mul] using
      mul_le_mul_of_nonneg_right hc (sq_nonneg (g x))
  have hHint : (∫⁻ p : SpatialCoordinates d × SpatialCoordinates d, H p) = D := by
    rw [Measure.volume_eq_prod, lintegral_prod _ hH.aemeasurable]
    calc
      _ = ∫⁻ x : SpatialCoordinates d, U.indicator
          (fun x => ∫⁻ y in U, cubeFractionalKernel s f x y) x := by
        apply lintegral_congr
        intro x
        by_cases hx : x ∈ U
        · rw [Set.indicator_of_mem hx]
          change (∫⁻ y : SpatialCoordinates d,
            if x ∈ U ∧ y ∈ U then cubeFractionalKernel s f x y else 0) = _
          simpa only [hx, true_and, Set.indicator] using
            lintegral_indicator hUm (fun y => cubeFractionalKernel s f x y)
        · simp only [H, hx, false_and, ite_false, lintegral_zero, Set.indicator_of_notMem hx]
      _ = D := lintegral_indicator hUm _
  have hRint : (∫⁻ p : SpatialCoordinates d × SpatialCoordinates d, R p) =
      4 * fractionalCutoffKernelMass d s * I := by
    rw [Measure.volume_eq_prod, lintegral_prod _ hR.aemeasurable]
    change (∫⁻ x : SpatialCoordinates d, ∫⁻ y : SpatialCoordinates d,
      2 * (ENNReal.ofReal (g x ^ 2) + ENNReal.ofReal (g y ^ 2)) *
        fractionalCutoffKernel s (x - y)) = _
    rw [double_lintegral_fractionalCutoffKernel s g hg, hI]
  have hfrac : (∫⁻ p : SpatialCoordinates d × SpatialCoordinates d,
      cubeFractionalKernel s V p.1 p.2) ≤ 2 * D + 4 * fractionalCutoffKernelMass d s * I := by
    calc
      _ ≤ ∫⁻ p : SpatialCoordinates d × SpatialCoordinates d, 2 * H p + R p := by
        apply lintegral_mono
        intro p
        exact cubeFractionalKernel_cutoffExtension_le s hs U f hU p.1 p.2
      _ = 2 * (∫⁻ p : SpatialCoordinates d × SpatialCoordinates d, H p) +
          ∫⁻ p : SpatialCoordinates d × SpatialCoordinates d, R p := by
        rw [lintegral_add_left (show Measurable (fun p : SpatialCoordinates d × SpatialCoordinates d => 2 * H p) from by simpa using! measurable_const.mul hH), lintegral_const_mul' _ _ (by norm_num)]
      _ = _ := by rw [hHint, hRint]
  have heq : globalFractionalSqNorm s V =
      (∫⁻ x : SpatialCoordinates d, ENNReal.ofReal (V x ^ 2)) +
        ∫⁻ p : SpatialCoordinates d × SpatialCoordinates d, cubeFractionalKernel s V p.1 p.2 := by
    unfold globalFractionalSqNorm
    congr 1
    apply lintegral_congr
    intro p
    simp only [cubeFractionalKernel, euclideanDist, euclideanNorm, vecNormSq, vecDot,
      Pi.sub_apply, ← pow_two]
  rw [heq]
  calc
    _ ≤ I + (2 * D + 4 * fractionalCutoffKernelMass d s * I) := add_le_add hL hfrac
    _ = _ := by ring

end SubdiffusiveProcess
