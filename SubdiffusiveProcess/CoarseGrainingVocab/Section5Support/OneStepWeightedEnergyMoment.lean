module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepRemainderSolution
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepWeightedCubicMeasurability

@[expose] public section

/-!
# Moment closure for the nonlinear one-step weighted energy

This file supplies the Holder calculation 
and its Neumann counterpart.  The nonlinear corrector is
split into its odd linear response and the exponential residual.  The
lemmas below keep the spatial average normalized and expose only fourth
moments, so the exact shell-negation cancellation can be inserted before
the thermodynamic passage.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-! ## Normalized Holder lemmas -/

local instance holderTripleFourFourTwo :
    ENNReal.HolderTriple (4 : ℝ≥0∞) (4 : ℝ≥0∞) (2 : ℝ≥0∞) :=
  { inv_add_inv_eq_inv := by
      rw [← two_mul]
      have h4 : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
      rw [h4, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul] }

private theorem cubeLpNorm_two_mul_le_four_mul_four {d : ℕ}
    (Q : TriadicCube d) (f g : Vec d → ℝ)
    (hf : MemLp f 4 (normalizedCubeMeasure Q))
    (hg : MemLp g 4 (normalizedCubeMeasure Q)) :
    cubeLpNorm Q 2 (fun x ↦ f x * g x) ≤
      cubeLpNorm Q 4 f * cubeLpNorm Q 4 g := by
  have hraw : eLpNorm (fun x ↦ f x * g x) 2
      (normalizedCubeMeasure Q) ≤
      eLpNorm f 4 (normalizedCubeMeasure Q) *
        eLpNorm g 4 (normalizedCubeMeasure Q) := by
    simpa using! eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (fun a b : ℝ ↦ a * b) 1 continuous_mul
        hf.aestronglyMeasurable hg.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ by simp)
  unfold cubeLpNorm
  simpa only [ENNReal.toReal_mul] using!
    (ENNReal.toReal_mono
      (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) hraw)

private theorem cubeLpNorm_two_le_four {d : ℕ}
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MemLp f 4 (normalizedCubeMeasure Q)) :
    cubeLpNorm Q 2 f ≤ cubeLpNorm Q 4 f := by
  have hraw : eLpNorm f 2 (normalizedCubeMeasure Q) ≤
      eLpNorm f 4 (normalizedCubeMeasure Q) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (f := f) (μ := normalizedCubeMeasure Q) (by norm_num : (2 : ℝ≥0∞) ≤ 4) hf.aestronglyMeasurable
    simpa [normalizedCubeMeasure_apply_univ] using! h
  unfold cubeLpNorm
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top hraw

/-- Three-factor Holder on a normalized cube, written only with fourth
norms. -/
theorem abs_cubeAverage_triple_le_four {d : ℕ}
    (Q : TriadicCube d) (f g k : Vec d → ℝ)
    (hf : MemLp f 4 (normalizedCubeMeasure Q))
    (hg : MemLp g 4 (normalizedCubeMeasure Q))
    (hk : MemLp k 4 (normalizedCubeMeasure Q)) :
    |cubeAverage Q (fun x ↦ f x * g x * k x)| ≤
      cubeLpNorm Q 4 f * cubeLpNorm Q 4 g * cubeLpNorm Q 4 k := by
  have hfg : MemLp (fun x ↦ f x * g x) 2
      (normalizedCubeMeasure Q) := by
    simpa only [Pi.mul_apply] using! hf.mul (r := 2) hg
  have hk2 : MemLp k 2 (normalizedCubeMeasure Q) := hk.mono_exponent (by norm_num)
  have htwo := abs_cubeAverage_mul_le_mul_cubeLpNorm_of_holderConjugate
    Q 2 2 (fun x ↦ f x * g x) k hfg hk2
  calc
    |cubeAverage Q (fun x ↦ f x * g x * k x)| ≤
        cubeLpNorm Q 2 (fun x ↦ f x * g x) * cubeLpNorm Q 2 k := htwo
    _ ≤ (cubeLpNorm Q 4 f * cubeLpNorm Q 4 g) * cubeLpNorm Q 4 k :=
      mul_le_mul (cubeLpNorm_two_mul_le_four_mul_four Q f g hf hg)
        (cubeLpNorm_two_le_four Q k hk)
        (cubeLpNorm_nonneg Q 2 k)
        (mul_nonneg (cubeLpNorm_nonneg Q 4 f) (cubeLpNorm_nonneg Q 4 g))
    _ = _ := by ring

theorem cubeLpNorm_norm_add_norm_le {d : ℕ}
    (Q : TriadicCube d) (u v : Vec d → HilbertVec d)
    (hu : MemLp u 4 (normalizedCubeMeasure Q))
    (hv : MemLp v 4 (normalizedCubeMeasure Q)) :
    cubeLpNorm Q 4 (fun x ↦ ‖u x‖ + ‖v x‖) ≤
      cubeLpNorm Q 4 (fun x ↦ ‖u x‖) +
        cubeLpNorm Q 4 (fun x ↦ ‖v x‖) := by
  have hraw := eLpNorm_add_le (μ := normalizedCubeMeasure Q) (f := fun x ↦ ‖u x‖) (g := fun x ↦ ‖v x‖) (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  unfold cubeLpNorm
  have htop : eLpNorm (fun x ↦ ‖u x‖) 4 (normalizedCubeMeasure Q) +
      eLpNorm (fun x ↦ ‖v x‖) 4 (normalizedCubeMeasure Q) ≠ ∞ :=
    ENNReal.add_ne_top.mpr
      ⟨hu.norm.eLpNorm_ne_top, hv.norm.eLpNorm_ne_top⟩
  have hreal := ENNReal.toReal_mono htop (by simpa only [Pi.add_apply] using! hraw)
  rw [ENNReal.toReal_add hu.norm.eLpNorm_ne_top hv.norm.eLpNorm_ne_top] at hreal
  exact hreal

theorem cubeLpNorm_norm_add_norm_le_two_add_remainder {d : ℕ}
    (Q : TriadicCube d) (u v r : HilbertVectorL2 (openCubeSet Q))
    (hu : (u : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (v : Vec d → HilbertVec d) + (r : Vec d → HilbertVec d))
    (hu4 : MemLp (u : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q))
    (hv4 : MemLp (v : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q))
    (hr4 : MemLp (r : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q)) :
    cubeLpNorm Q 4 (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖ +
        ‖(v : Vec d → HilbertVec d) x‖) ≤
      2 * cubeLpNorm Q 4 (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖) +
        cubeLpNorm Q 4 (fun x ↦ ‖(r : Vec d → HilbertVec d) x‖) := by
  have hfirst := cubeLpNorm_norm_add_norm_le Q
    (u : Vec d → HilbertVec d) (v : Vec d → HilbertVec d) hu4 hv4
  have hvEq : (v : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (u : Vec d → HilbertVec d) - (r : Vec d → HilbertVec d) := by
    filter_upwards [hu] with x hx
    change (u : Vec d → HilbertVec d) x =
      (v : Vec d → HilbertVec d) x + (r : Vec d → HilbertVec d) x at hx
    change (v : Vec d → HilbertVec d) x =
      (u : Vec d → HilbertVec d) x - (r : Vec d → HilbertVec d) x
    rw [hx]
    abel
  have hvNorm : cubeLpNorm Q 4 (fun x ↦
      ‖(v : Vec d → HilbertVec d) x‖) ≤
      cubeLpNorm Q 4 (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖) +
        cubeLpNorm Q 4 (fun x ↦ ‖(r : Vec d → HilbertVec d) x‖) := by
    unfold cubeLpNorm
    have hcongr : eLpNorm (v : Vec d → HilbertVec d) 4
        (normalizedCubeMeasure Q) =
        eLpNorm (fun x ↦ (u : Vec d → HilbertVec d) x - r x) 4
          (normalizedCubeMeasure Q) := eLpNorm_congr_ae hvEq
    rw [eLpNorm_norm _ hv4.aestronglyMeasurable,
      eLpNorm_norm _ hu4.aestronglyMeasurable,
      eLpNorm_norm _ hr4.aestronglyMeasurable, hcongr]
    have hsub := eLpNorm_sub_le (μ := normalizedCubeMeasure Q) (f := (u : Vec d → HilbertVec d)) (g := (r : Vec d → HilbertVec d)) (by norm_num : (1 : ℝ≥0∞) ≤ 4)
    have hsub' : eLpNorm (fun x ↦
        (u : Vec d → HilbertVec d) x - (r : Vec d → HilbertVec d) x) 4
        (normalizedCubeMeasure Q) ≤
        eLpNorm (u : Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q) +
          eLpNorm (r : Vec d → HilbertVec d) 4
            (normalizedCubeMeasure Q) := by
      simpa only [Pi.sub_apply] using! hsub
    have hreal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr
        ⟨hu4.eLpNorm_ne_top, hr4.eLpNorm_ne_top⟩) hsub'
    rw [ENNReal.toReal_add hu4.eLpNorm_ne_top hr4.eLpNorm_ne_top] at hreal
    exact hreal
  calc
    _ ≤ cubeLpNorm Q 4 (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖) +
        cubeLpNorm Q 4 (fun x ↦ ‖(v : Vec d → HilbertVec d) x‖) := hfirst
    _ ≤ cubeLpNorm Q 4 (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖) +
        (cubeLpNorm Q 4 (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖) +
          cubeLpNorm Q 4 (fun x ↦ ‖(r : Vec d → HilbertVec d) x‖)) :=
      add_le_add le_rfl hvNorm
    _ = _ := by ring

/-! ## Deterministic nonlinear comparison -/

private theorem abs_norm_sq_sub_norm_sq_le
    {E : Type*} [NormedAddCommGroup E] (u v r : E) (hu : u = v + r) :
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ ‖r‖ * (‖u‖ + ‖v‖) := by
  have hdiff : u - v = r := by rw [hu]; abel
  calc
    |‖u‖ ^ 2 - ‖v‖ ^ 2| = |‖u‖ - ‖v‖| * (‖u‖ + ‖v‖) := by
      rw [show ‖u‖ ^ 2 - ‖v‖ ^ 2 = (‖u‖ - ‖v‖) * (‖u‖ + ‖v‖) by ring,
        abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    _ ≤ ‖u - v‖ * (‖u‖ + ‖v‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le u v)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by rw [hdiff]

/-- Pointwise form of the weighted-energy replacement.  It is stated for
the Hilbert representatives used by the measurable cubic functional. -/
theorem abs_weightedQuadratic_sub_linear_le
    {d : ℕ} (p u v r z e : HilbertVec d)
    (hp : ‖p‖ ≤ 1) (hu : u = v + r) :
    |‖u‖ ^ 2 * inner ℝ p (z + e) - ‖v‖ ^ 2 * inner ℝ p z| ≤
      ‖r‖ * (‖u‖ + ‖v‖) * ‖z‖ + ‖u‖ * ‖u‖ * ‖e‖ := by
  have hz : |inner ℝ p z| ≤ ‖z‖ :=
    (abs_real_inner_le_norm p z).trans (by
      simpa only [one_mul] using! mul_le_mul_of_nonneg_right hp (norm_nonneg z))
  have he : |inner ℝ p e| ≤ ‖e‖ :=
    (abs_real_inner_le_norm p e).trans (by
      simpa only [one_mul] using! mul_le_mul_of_nonneg_right hp (norm_nonneg e))
  have hsq := abs_norm_sq_sub_norm_sq_le u v r hu
  rw [inner_add_right]
  have hid : ‖u‖ ^ 2 * (inner ℝ p z + inner ℝ p e) -
      ‖v‖ ^ 2 * inner ℝ p z =
      (‖u‖ ^ 2 - ‖v‖ ^ 2) * inner ℝ p z +
        ‖u‖ ^ 2 * inner ℝ p e := by ring
  rw [hid]
  calc
    |(‖u‖ ^ 2 - ‖v‖ ^ 2) * inner ℝ p z +
        ‖u‖ ^ 2 * inner ℝ p e| ≤
        |‖u‖ ^ 2 - ‖v‖ ^ 2| * |inner ℝ p z| +
          ‖u‖ ^ 2 * |inner ℝ p e| := by
      calc
        _ ≤ |(‖u‖ ^ 2 - ‖v‖ ^ 2) * inner ℝ p z| +
            |‖u‖ ^ 2 * inner ℝ p e| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ‖u‖)]
    _ ≤ (‖r‖ * (‖u‖ + ‖v‖)) * ‖z‖ + ‖u‖ ^ 2 * ‖e‖ := by
      exact add_le_add
        (mul_le_mul hsq hz (abs_nonneg _) (mul_nonneg (norm_nonneg _)
          (add_nonneg (norm_nonneg _) (norm_nonneg _))))
        (mul_le_mul_of_nonneg_left he (sq_nonneg _))
    _ = _ := by ring

/-- Spatially averaged comparison, in the exact fourth-moment form used by
the stochastic closure. -/
theorem abs_cubeAverage_weightedQuadratic_sub_linear_le_four
    {d : ℕ} (Q : TriadicCube d) (p : HilbertVec d)
    (u v r z e : Vec d → HilbertVec d)
    (hp : ‖p‖ ≤ 1) (hu : u =ᵐ[normalizedCubeMeasure Q] v + r)
    (hu4 : MemLp u 4 (normalizedCubeMeasure Q))
    (hv4 : MemLp v 4 (normalizedCubeMeasure Q))
    (hr4 : MemLp r 4 (normalizedCubeMeasure Q))
    (hz4 : MemLp z 4 (normalizedCubeMeasure Q))
    (he4 : MemLp e 4 (normalizedCubeMeasure Q)) :
    |cubeAverage Q (fun x ↦
        ‖u x‖ ^ 2 * inner ℝ p (z x + e x) -
          ‖v x‖ ^ 2 * inner ℝ p (z x))| ≤
      cubeLpNorm Q 4 (fun x ↦ ‖r x‖) *
          cubeLpNorm Q 4 (fun x ↦ ‖u x‖ + ‖v x‖) *
          cubeLpNorm Q 4 (fun x ↦ ‖z x‖) +
        cubeLpNorm Q 4 (fun x ↦ ‖u x‖) *
          cubeLpNorm Q 4 (fun x ↦ ‖u x‖) *
          cubeLpNorm Q 4 (fun x ↦ ‖e x‖) := by
  let lhs : Vec d → ℝ := fun x ↦
    ‖u x‖ ^ 2 * inner ℝ p (z x + e x) -
      ‖v x‖ ^ 2 * inner ℝ p (z x)
  let a : Vec d → ℝ := fun x ↦ ‖r x‖
  let b : Vec d → ℝ := fun x ↦ ‖u x‖ + ‖v x‖
  let c : Vec d → ℝ := fun x ↦ ‖z x‖
  let q : Vec d → ℝ := fun x ↦ ‖u x‖
  let s : Vec d → ℝ := fun x ↦ ‖e x‖
  have ha4 : MemLp a 4 (normalizedCubeMeasure Q) := hr4.norm
  have hb4 : MemLp b 4 (normalizedCubeMeasure Q) := hu4.norm.add hv4.norm
  have hc4 : MemLp c 4 (normalizedCubeMeasure Q) := hz4.norm
  have hq4 : MemLp q 4 (normalizedCubeMeasure Q) := hu4.norm
  have hs4 : MemLp s 4 (normalizedCubeMeasure Q) := he4.norm
  have hfirst : MemLp (fun x ↦ a x * b x * c x) 1
      (normalizedCubeMeasure Q) := by
    have hab : MemLp (fun x ↦ a x * b x) 2
        (normalizedCubeMeasure Q) := by simpa only [Pi.mul_apply] using! ha4.mul (r := 2) hb4
    have hc2 := hc4.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)
    let : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) (1 : ℝ≥0∞) :=
      by infer_instance
    simpa only [Pi.mul_apply] using! hab.mul (r := 1) hc2
  have hsecond : MemLp (fun x ↦ q x * q x * s x) 1
      (normalizedCubeMeasure Q) := by
    have hqq : MemLp (fun x ↦ q x * q x) 2
        (normalizedCubeMeasure Q) := by simpa only [Pi.mul_apply] using! hq4.mul (r := 2) hq4
    have hs2 := hs4.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)
    let : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) (1 : ℝ≥0∞) :=
      by infer_instance
    simpa only [Pi.mul_apply] using! hqq.mul (r := 1) hs2
  have hlhs : Integrable lhs (normalizedCubeMeasure Q) := by
    have hmajor := hfirst.add hsecond
    have hlhsMeas : AEStronglyMeasurable lhs (normalizedCubeMeasure Q) := by
      have hze : AEStronglyMeasurable
          (fun x ↦ inner ℝ p (z x + e x)) (normalizedCubeMeasure Q) :=
        (hz4.aestronglyMeasurable.add he4.aestronglyMeasurable).const_inner
      have hz : AEStronglyMeasurable
          (fun x ↦ inner ℝ p (z x)) (normalizedCubeMeasure Q) :=
        hz4.aestronglyMeasurable.const_inner
      simpa only [lhs, pow_two, Pi.add_apply] using!
        ((hu4.aestronglyMeasurable.norm.mul hu4.aestronglyMeasurable.norm).mul hze |>.sub
          ((hv4.aestronglyMeasurable.norm.mul hv4.aestronglyMeasurable.norm).mul hz))
    apply (hmajor.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)).mono hlhsMeas
    filter_upwards [hu] with x hx
    have hpoint := abs_weightedQuadratic_sub_linear_le p (u x) (v x) (r x)
      (z x) (e x) hp hx
    have hmajor0 : 0 ≤ a x * b x * c x + q x * q x * s x := by
      dsimp only [a, b, c, q, s]
      positivity
    simpa only [Real.norm_eq_abs, abs_abs, lhs, a, b, c, q, s,
      Pi.add_apply, abs_of_nonneg hmajor0] using! hpoint
  calc
    |cubeAverage Q lhs| ≤ cubeAverage Q (fun x ↦ |lhs x|) := by
      rw [cubeAverage_eq_integral_normalizedCubeMeasure,
        cubeAverage_eq_integral_normalizedCubeMeasure]
      exact abs_integral_le_integral_abs
    _ ≤ cubeAverage Q (fun x ↦ a x * b x * c x + q x * q x * s x) := by
      rw [cubeAverage_eq_integral_normalizedCubeMeasure,
        cubeAverage_eq_integral_normalizedCubeMeasure]
      apply integral_mono_ae hlhs.abs
      · exact (hfirst.integrable (by norm_num)).add
          (hsecond.integrable (by norm_num))
      filter_upwards [hu] with x hx
      exact abs_weightedQuadratic_sub_linear_le p (u x) (v x) (r x)
        (z x) (e x) hp hx
    _ = cubeAverage Q (fun x ↦ a x * b x * c x) +
        cubeAverage Q (fun x ↦ q x * q x * s x) := by
      rw [cubeAverage_eq_integral_normalizedCubeMeasure,
        cubeAverage_eq_integral_normalizedCubeMeasure,
        cubeAverage_eq_integral_normalizedCubeMeasure]
      exact integral_add (hfirst.integrable (by norm_num))
        (hsecond.integrable (by norm_num))
    _ ≤ |cubeAverage Q (fun x ↦ a x * b x * c x)| +
        |cubeAverage Q (fun x ↦ q x * q x * s x)| :=
      add_le_add (le_abs_self _) (le_abs_self _)
    _ ≤ cubeLpNorm Q 4 a * cubeLpNorm Q 4 b * cubeLpNorm Q 4 c +
        cubeLpNorm Q 4 q * cubeLpNorm Q 4 q * cubeLpNorm Q 4 s :=
      add_le_add
        (abs_cubeAverage_triple_le_four Q a b c ha4 hb4 hc4)
        (abs_cubeAverage_triple_le_four Q q q s hq4 hq4 hs4)
    _ = _ := rfl

/-! ## Normalized measurable cubic -/

/-- The Borel weighted quadratic functional normalized by the cube volume. -/
def oneStepNormalizedWeightedCubicBorel {d : ℕ}
    (Q : TriadicCube d) (p : HilbertVec d)
    (F G : HilbertVectorL2 (openCubeSet Q)) : ℝ :=
  (cubeVolume Q)⁻¹ * oneStepWeightedCubicBorel p F G

theorem measurable_oneStepNormalizedWeightedCubicBorel {d : ℕ}
    (Q : TriadicCube d) (p : HilbertVec d) :
    Measurable fun FG :
        HilbertVectorL2 (openCubeSet Q) × HilbertVectorL2 (openCubeSet Q) ↦
      oneStepNormalizedWeightedCubicBorel Q p FG.1 FG.2 := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact (measurable_oneStepWeightedCubicBorel
    (U := openCubeSet Q) p).const_mul _

private theorem integrable_oneStepWeightedCubicIntegrand_of_memLp_four
    {d : ℕ} (Q : TriadicCube d) (p : HilbertVec d)
    (F G : HilbertVectorL2 (openCubeSet Q))
    (hF : MemLp (F : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q))
    (hG : MemLp (G : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q)) :
    Integrable (oneStepWeightedCubicIntegrand p F G)
      (normalizedCubeMeasure Q) := by
  have hFnorm4 := hF.norm
  have hFsq2 : MemLp (fun x ↦ ‖(F : Vec d → HilbertVec d) x‖ * ‖F x‖) 2
      (normalizedCubeMeasure Q) := by
    simpa only [Pi.mul_apply] using! hFnorm4.mul (r := 2) hFnorm4
  have hinner4 : MemLp (fun x ↦ inner ℝ p ((G : Vec d → HilbertVec d) x)) 4
      (normalizedCubeMeasure Q) := by
    exact (InnerProductSpace.toDual ℝ (HilbertVec d) p).comp_memLp' hG
  have hinner2 := hinner4.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)
  have : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) (1 : ℝ≥0∞) :=
    by infer_instance
  have hprod : MemLp (fun x ↦
      (‖(F : Vec d → HilbertVec d) x‖ * ‖F x‖) *
        inner ℝ p ((G : Vec d → HilbertVec d) x)) 1
      (normalizedCubeMeasure Q) := by
    simpa only [Pi.mul_apply] using! hFsq2.mul (r := 1) hinner2
  have hfun : oneStepWeightedCubicIntegrand p F G = fun x ↦
      (‖(F : Vec d → HilbertVec d) x‖ * ‖F x‖) *
        inner ℝ p ((G : Vec d → HilbertVec d) x) := by
    funext x
    rw [oneStepWeightedCubicIntegrand, pow_two]
  rw [hfun]
  exact hprod.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)

/-- On fourth-integrable inputs, the normalized Borel functional is the
literal normalized spatial average. -/
theorem oneStepNormalizedWeightedCubicBorel_eq_cubeAverage {d : ℕ}
    (Q : TriadicCube d) (p : HilbertVec d)
    (F G : HilbertVectorL2 (openCubeSet Q))
    (hF : MemLp (F : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q))
    (hG : MemLp (G : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q)) :
    oneStepNormalizedWeightedCubicBorel Q p F G =
      cubeAverage Q (oneStepWeightedCubicIntegrand p F G) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hintNorm := integrable_oneStepWeightedCubicIntegrand_of_memLp_four
    Q p F G hF hG
  have hintOpen : Integrable (oneStepWeightedCubicIntegrand p F G)
      (volumeMeasureOn (openCubeSet Q)) := by
    have hc0 : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (cubeVolume_pos Q))
    have hctop : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    have hcube : Integrable (oneStepWeightedCubicIntegrand p F G)
        (cubeMeasure Q) := by
      exact (integrable_smul_measure hc0 hctop).mp (by
        simpa only [normalizedCubeMeasure] using! hintNorm)
    have hcubeOn : IntegrableOn (oneStepWeightedCubicIntegrand p F G)
        (cubeSet Q) volume := by
      simpa only [cubeMeasure] using! hcube
    have hopenOn : IntegrableOn (oneStepWeightedCubicIntegrand p F G)
        (openCubeSet Q) volume :=
      integrableOn_cubeSet_iff_integrableOn_openCubeSet.mp hcubeOn
    simpa only [volumeMeasureOn] using! hopenOn
  rw [oneStepNormalizedWeightedCubicBorel,
    oneStepWeightedCubicBorel_eq_integral p F G hintOpen,
    oneStepWeightedCubicIntegral, cubeAverage]
  rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet]



theorem abs_oneStepNormalizedWeightedCubicBorel_sub_le_four {d : ℕ}
    (Q : TriadicCube d) (p : HilbertVec d)
    (u v r z e : HilbertVectorL2 (openCubeSet Q))
    (hp : ‖p‖ ≤ 1)
    (hu : (u : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (v : Vec d → HilbertVec d) + (r : Vec d → HilbertVec d))
    (hu4 : MemLp (u : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q))
    (hv4 : MemLp (v : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q))
    (hr4 : MemLp (r : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q))
    (hz4 : MemLp (z : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q))
    (he4 : MemLp (e : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q)) :
    |oneStepNormalizedWeightedCubicBorel Q p u (z + e) -
        oneStepNormalizedWeightedCubicBorel Q p v z| ≤
      cubeLpNorm Q 4 (fun x ↦ ‖(r : Vec d → HilbertVec d) x‖) *
          cubeLpNorm Q 4 (fun x ↦
            ‖(u : Vec d → HilbertVec d) x‖ +
              ‖(v : Vec d → HilbertVec d) x‖) *
          cubeLpNorm Q 4 (fun x ↦ ‖(z : Vec d → HilbertVec d) x‖) +
        cubeLpNorm Q 4 (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖) *
          cubeLpNorm Q 4 (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖) *
          cubeLpNorm Q 4 (fun x ↦ ‖(e : Vec d → HilbertVec d) x‖) := by
  have hadd : ((z + e : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (z : Vec d → HilbertVec d) + (e : Vec d → HilbertVec d) := by
    apply Gagliardo.ae_normalizedCubeMeasure_iff.2
    simpa only [cubeMeasure, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using!
      Lp.coeFn_add z e
  have hze4 : MemLp ((z + e : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q) := by
    exact (hz4.add he4).ae_eq hadd.symm
  rw [oneStepNormalizedWeightedCubicBorel_eq_cubeAverage Q p u (z + e) hu4 hze4,
    oneStepNormalizedWeightedCubicBorel_eq_cubeAverage Q p v z hv4 hz4]
  have hfirst := integrable_oneStepWeightedCubicIntegrand_of_memLp_four
    Q p u (z + e) hu4 hze4
  have hsecond := integrable_oneStepWeightedCubicIntegrand_of_memLp_four
    Q p v z hv4 hz4
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure,
    ← integral_sub hfirst hsecond,
    ← cubeAverage_eq_integral_normalizedCubeMeasure]
  have havg : cubeAverage Q (fun x ↦
      oneStepWeightedCubicIntegrand p u (z + e) x -
        oneStepWeightedCubicIntegrand p v z x) =
      cubeAverage Q (fun x ↦
        ‖(u : Vec d → HilbertVec d) x‖ ^ 2 *
            inner ℝ p ((z : Vec d → HilbertVec d) x + e x) -
          ‖(v : Vec d → HilbertVec d) x‖ ^ 2 *
            inner ℝ p ((z : Vec d → HilbertVec d) x)) := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure]
    apply integral_congr_ae
    filter_upwards [hadd] with x hx
    rw [oneStepWeightedCubicIntegrand, oneStepWeightedCubicIntegrand, hx]
    rfl
  rw [havg]
  exact abs_cubeAverage_weightedQuadratic_sub_linear_le_four Q p
    (u : Vec d → HilbertVec d) (v : Vec d → HilbertVec d)
    (r : Vec d → HilbertVec d) (z : Vec d → HilbertVec d)
    (e : Vec d → HilbertVec d) hp hu hu4 hv4 hr4 hz4 he4

/-! ## Borel normalized fourth norms -/

theorem normalizedCubeMeasure_eq_smul_volumeMeasureOn_openCubeSet
    {d : ℕ} (Q : TriadicCube d) :
    normalizedCubeMeasure Q =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) •
        volumeMeasureOn (openCubeSet Q) := by
  rw [normalizedCubeMeasure, cubeMeasure, volumeMeasureOn,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- An `ENNReal`-valued Borel representative of the normalized spatial `L⁴`
norm of an
`L²` class.  The fourth mass is built by monotone truncation in
`OneStepWeightedCubicMeasurability`; the normalization converts its ambient
open-cube measure to the manuscript's probability measure. -/
def oneStepNormalizedFourthNormENNRealBorel {d : ℕ} (Q : TriadicCube d)
    (F : HilbertVectorL2 (openCubeSet Q)) : ℝ≥0∞ :=
  (ENNReal.ofReal ((cubeVolume Q)⁻¹) *
      oneStepFourthMassBorel F) ^ (1 / 4 : ℝ)

/-- Real-valued form of `oneStepNormalizedFourthNormENNRealBorel`. -/
def oneStepNormalizedFourthNormBorel {d : ℕ} (Q : TriadicCube d)
    (F : HilbertVectorL2 (openCubeSet Q)) : ℝ :=
  (oneStepNormalizedFourthNormENNRealBorel Q F).toReal

theorem measurable_oneStepNormalizedFourthNormENNRealBorel {d : ℕ}
    (Q : TriadicCube d) :
    Measurable (oneStepNormalizedFourthNormENNRealBorel Q) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact ((measurable_oneStepFourthMassBorel
    (d := d) (U := openCubeSet Q)).const_mul _).pow_const _

theorem measurable_oneStepNormalizedFourthNormBorel {d : ℕ}
    (Q : TriadicCube d) :
    Measurable (oneStepNormalizedFourthNormBorel Q) := by
  exact (measurable_oneStepNormalizedFourthNormENNRealBorel Q).ennreal_toReal

private theorem weightedEnergy_aestronglyMeasurable_normalized {d : ℕ}
    (Q : TriadicCube d) (F : HilbertVectorL2 (openCubeSet Q)) :
    AEStronglyMeasurable (F : Vec d → HilbertVec d) (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure_eq_smul_volumeMeasureOn_openCubeSet]
  exact (Lp.aestronglyMeasurable F).smul_measure _

theorem oneStepNormalizedFourthNormENNRealBorel_eq_eLpNorm {d : ℕ}
    (Q : TriadicCube d) (F : HilbertVectorL2 (openCubeSet Q)) :
    oneStepNormalizedFourthNormENNRealBorel Q F =
      eLpNorm (fun x ↦ ‖(F : Vec d → HilbertVec d) x‖) 4
        (normalizedCubeMeasure Q) := by
  unfold oneStepNormalizedFourthNormENNRealBorel
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) ((weightedEnergy_aestronglyMeasurable_normalized Q F).norm)]
  norm_num only [ENNReal.toReal_ofNat]
  rw [normalizedCubeMeasure_eq_smul_volumeMeasureOn_openCubeSet,
    lintegral_smul_measure]
  simp only [smul_eq_mul, oneStepFourthMassBorel]
  congr 2
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (norm_nonneg _),
    ← ofReal_norm]

theorem oneStepNormalizedFourthNormENNRealBorel_eq_eLpNorm_coe {d : ℕ}
    (Q : TriadicCube d) (F : HilbertVectorL2 (openCubeSet Q)) :
    oneStepNormalizedFourthNormENNRealBorel Q F =
      eLpNorm (F : Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q) := by
  rw [oneStepNormalizedFourthNormENNRealBorel_eq_eLpNorm,
    eLpNorm_norm _ (weightedEnergy_aestronglyMeasurable_normalized Q F)]

theorem oneStepNormalizedFourthNormENNRealBorel_eq_eLpNorm_of_ae
    {d : ℕ} (Q : TriadicCube d)
    (F : HilbertVectorL2 (openCubeSet Q)) (f : Vec d → HilbertVec d)
    (hF : (F : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q] f) :
    oneStepNormalizedFourthNormENNRealBorel Q F =
      eLpNorm f 4 (normalizedCubeMeasure Q) := by
  rw [oneStepNormalizedFourthNormENNRealBorel_eq_eLpNorm_coe]
  exact eLpNorm_congr_ae hF

theorem oneStepNormalizedFourthNormBorel_eq_cubeLpNorm {d : ℕ}
    (Q : TriadicCube d) (F : HilbertVectorL2 (openCubeSet Q)) :
    oneStepNormalizedFourthNormBorel Q F =
      cubeLpNorm Q 4 (fun x ↦ ‖(F : Vec d → HilbertVec d) x‖) := by
  rw [oneStepNormalizedFourthNormBorel, cubeLpNorm,
    oneStepNormalizedFourthNormENNRealBorel_eq_eLpNorm]

theorem oneStepFourthNormMajorant_le_borel {d : ℕ}
    (Q : TriadicCube d) (u v r z e : HilbertVectorL2 (openCubeSet Q))
    (hu : (u : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (v : Vec d → HilbertVec d) + (r : Vec d → HilbertVec d))
    (hu4 : MemLp (u : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q))
    (hv4 : MemLp (v : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q))
    (hr4 : MemLp (r : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q)) :
    cubeLpNorm Q 4 (fun x ↦ ‖(r : Vec d → HilbertVec d) x‖) *
          cubeLpNorm Q 4 (fun x ↦
            ‖(u : Vec d → HilbertVec d) x‖ +
              ‖(v : Vec d → HilbertVec d) x‖) *
          cubeLpNorm Q 4 (fun x ↦ ‖(z : Vec d → HilbertVec d) x‖) +
        cubeLpNorm Q 4 (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖) *
          cubeLpNorm Q 4 (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖) *
          cubeLpNorm Q 4 (fun x ↦ ‖(e : Vec d → HilbertVec d) x‖) ≤
      oneStepNormalizedFourthNormBorel Q r *
          (2 * oneStepNormalizedFourthNormBorel Q u +
            oneStepNormalizedFourthNormBorel Q r) *
          oneStepNormalizedFourthNormBorel Q z +
        oneStepNormalizedFourthNormBorel Q u *
          oneStepNormalizedFourthNormBorel Q u *
          oneStepNormalizedFourthNormBorel Q e := by
  have hmiddle := cubeLpNorm_norm_add_norm_le_two_add_remainder
    Q u v r hu hu4 hv4 hr4
  rw [oneStepNormalizedFourthNormBorel_eq_cubeLpNorm,
    oneStepNormalizedFourthNormBorel_eq_cubeLpNorm,
    oneStepNormalizedFourthNormBorel_eq_cubeLpNorm,
    oneStepNormalizedFourthNormBorel_eq_cubeLpNorm]
  exact add_le_add
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmiddle (cubeLpNorm_nonneg Q 4 _))
      (cubeLpNorm_nonneg Q 4 _)) le_rfl

/-! ## Canonical one-step observables -/

theorem ae_normalizedCubeMeasure_of_ae_volumeMeasureOn
    {d : ℕ} (Q : TriadicCube d) {E : Type*}
    [NormedAddCommGroup E] {f g : Vec d → E}
    (hfg : f =ᵐ[volumeMeasureOn (openCubeSet Q)] g) :
    f =ᵐ[normalizedCubeMeasure Q] g := by
  apply Gagliardo.ae_normalizedCubeMeasure_iff.2
  simpa only [cubeMeasure, volumeMeasureOn,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using! hfg

theorem memLp_four_oneStepContinuousScalarForcingL2
    {d : ℕ} (Q : TriadicCube d) (p : Vec d) (f : C(Vec d, ℝ)) :
    MemLp (oneStepContinuousScalarForcingL2 Q p f :
      Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q) := by
  let F : Vec d → HilbertVec d := fun x ↦ f x • HilbertVec.ofVec p
  let L : ℝ →L[ℝ] HilbertVec d :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (HilbertVec.ofVec p)
  have hf : MemLp (fun x ↦ f x) 4 (normalizedCubeMeasure Q) :=
    SubdiffusiveProcess.CoarseGrainingVocab.memLp_normalizedCubeMeasure_of_continuous
      Q (4 : ℝ≥0∞) f.continuous
  have hF : MemLp F 4 (normalizedCubeMeasure Q) := by
    simpa only [F, L, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self] using! hf.continuousLinearMap_comp L
  have hcoe : (oneStepContinuousScalarForcingL2 Q p f :
      Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q] F := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    exact coeFn_toHilbertVectorL2OfVecField
      (memVectorL2_openCubeSet_of_continuous Q
        (f.continuous.smul (continuous_const : Continuous fun _ : Vec d ↦ p)))
  exact hF.ae_eq hcoe.symm

theorem memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure
    {d : ℕ} (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (hu : MemLp (hilbertifyVecField u.grad) 4
      (normalizedCubeMeasure Q)) :
    MemLp (u.gradToHilbertVectorL2 : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
  have hcoe : (u.gradToHilbertVectorL2 : Vec d → HilbertVec d) =ᵐ[
      normalizedCubeMeasure Q] hilbertifyVecField u.grad :=
    ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      u.coeFn_gradToHilbertVectorL2
  exact hu.ae_eq hcoe.symm

/-- Universal fourth-moment constant for the uncentered linear shell. -/
noncomputable def oneStepLinearShellFourConst : ℝ≥0∞ :=
  ENNReal.ofReal
    (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt 4 *
      cutoffGammaConst)

/-- Mixed spatial--random fourth moment of the uncentered shell block. -/
theorem lintegral_lintegral_cutoffShellSum_four_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (m : ℤ)
    (hh : 0 < h) :
    ∫⁻ omega, ∫⁻ x,
        ‖cutoffShellSum (n + h) (n : ℤ) x omega‖ₑ ^ (4 : ℝ)
          ∂normalizedCubeMeasure (originCube d m) ∂M.P.toMeasure ≤
      (oneStepLinearShellFourConst *
        ENNReal.ofReal (M.delta * Real.sqrt (h : ℝ))) ^ (4 : ℝ) := by
  let Q := originCube d m
  let R : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d → ℝ := fun q ↦
    cutoffShellSum (n + h) (n : ℤ) q.2 q.1
  have hR : Measurable R := by
    simpa only [R] using! measurable_cutoffShellSum_uncurry n h
  have hjoint : AEMeasurable
      (Function.uncurry fun omega x ↦ ‖R (omega, x)‖ₑ ^ (4 : ℝ))
      (M.P.toMeasure.prod (normalizedCubeMeasure Q)) := by
    simpa only [Function.uncurry_apply_pair] using!
      (hR.enorm.pow_const (4 : ℝ)).aemeasurable
  rw [lintegral_lintegral_swap hjoint]
  have hpoint : ∀ᵐ x ∂normalizedCubeMeasure Q,
      ∫⁻ omega, ‖R (omega, x)‖ₑ ^ (4 : ℝ) ∂M.P.toMeasure ≤
        (oneStepLinearShellFourConst *
          ENNReal.ofReal (M.delta * Real.sqrt (h : ℝ))) ^ (4 : ℝ) := by
    filter_upwards with x
    let X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ R (omega, x)
    let A : ℝ := cutoffGammaConst * Real.sqrt (h : ℝ) * M.delta
    have hA : 0 < A := by
      exact mul_pos (mul_pos cutoffGammaConst_pos
        (Real.sqrt_pos.mpr (by exact_mod_cast hh))) M.shellPrefix.delta_pos
    have hnorm : eLpNorm X 4 M.P.toMeasure ≤
        oneStepLinearShellFourConst *
          ENNReal.ofReal (M.delta * Real.sqrt (h : ℝ)) := by
      have hdiff : ((n + h : ℕ) : ℤ) - (n : ℤ) = (h : ℤ) := by omega
      have hsource :=
        isBigO_gammaTwo_cutoffShellSum_sourceScale M (n + h) (n : ℤ) x
          (by omega) (by omega)
      rw [hdiff] at hsource
      have hraw := eLpNorm_le_of_isBigO_gammaTwo
        (mu := M.P.toMeasure) (X := X) (A := A) (p := 4)
        hA (by norm_num)
        (by simpa only [X, R] using!
          (measurable_cutoffShellSum (n + h) (n : ℤ) x).aemeasurable)
        (by simpa only [X, R, A, Int.cast_natCast] using! hsource)
      calc
        eLpNorm X 4 M.P.toMeasure ≤
            ENNReal.ofReal
              (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt 4 * A) := by
          simpa using! hraw
        _ = oneStepLinearShellFourConst *
            ENNReal.ofReal (M.delta * Real.sqrt (h : ℝ)) := by
          unfold oneStepLinearShellFourConst
          rw [← ENNReal.ofReal_mul (mul_nonneg
            (mul_nonneg
              (Homogenization.IndependentSums.gammaMomentConst_pos
                (by norm_num)).le
              (Real.sqrt_nonneg 4)) cutoffGammaConst_pos.le)]
          congr 1
          dsimp only [A]
          ring
    have hpow := ENNReal.rpow_le_rpow hnorm (by norm_num : (0 : ℝ) ≤ 4)
    have hXmeas : AEStronglyMeasurable X M.P.toMeasure :=
      (hR.comp (measurable_id.prodMk (measurable_const (a := x)))).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := X) (by norm_num)
      (by norm_num) hXmeas] at hpow
    norm_num only [ENNReal.toReal_ofNat] at hpow
    have hquarter : (1 / 4 : ℝ) = (4 : ℝ)⁻¹ := by norm_num
    rw [hquarter, ENNReal.rpow_inv_rpow (by norm_num : (4 : ℝ) ≠ 0)] at hpow
    simpa only [X, R, ENNReal.rpow_natCast] using! hpow
  calc
    (∫⁻ x, ∫⁻ omega, ‖R (omega, x)‖ₑ ^ (4 : ℝ)
        ∂M.P.toMeasure ∂normalizedCubeMeasure Q) ≤
      ∫⁻ _x, (oneStepLinearShellFourConst *
        ENNReal.ofReal (M.delta * Real.sqrt (h : ℝ))) ^ (4 : ℝ)
          ∂normalizedCubeMeasure Q := lintegral_mono_ae hpoint
    _ = _ := by
      rw [lintegral_const]
      simp [normalizedCubeMeasure_apply_univ]

/-- Convert an explicit fourth moment of an `ENNReal` norm observable into
the ordinary real `MemLp`/`eLpNorm` interface used by probability Hölder. -/
private theorem memLp_toReal_four_and_eLpNorm_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (F : Omega → ℝ≥0∞) (A : ℝ≥0∞)
    (hF : Measurable F) (hFtop : ∀ omega, F omega ≠ ∞)
    (hA : A < ∞)
    (hmoment : ∫⁻ omega, (F omega) ^ (4 : ℝ) ∂mu ≤ A ^ (4 : ℝ)) :
    MemLp (fun omega ↦ (F omega).toReal) 4 mu ∧
      eLpNorm (fun omega ↦ (F omega).toReal) 4 mu ≤ A := by
  have hmeas : AEStronglyMeasurable (fun omega ↦ (F omega).toReal) mu :=
    hF.ennreal_toReal.aestronglyMeasurable
  have hnorm : eLpNorm (fun omega ↦ (F omega).toReal) 4 mu =
      (∫⁻ omega, (F omega) ^ (4 : ℝ) ∂mu) ^ (1 / 4 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (hmeas)]
    congr 2
    funext omega
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hFtop omega)]
    norm_num
  have hroot : (∫⁻ omega, (F omega) ^ (4 : ℝ) ∂mu) ^ (1 / 4 : ℝ) ≤ A := by
    calc
      _ ≤ (A ^ (4 : ℝ)) ^ (1 / 4 : ℝ) :=
        ENNReal.rpow_le_rpow hmoment (by norm_num)
      _ = A := by
        rw [← ENNReal.rpow_mul]
        norm_num
  have hbound : eLpNorm (fun omega ↦ (F omega).toReal) 4 mu ≤ A := by
    rw [hnorm]
    exact hroot
  exact ⟨hbound.trans_lt hA, hbound⟩

/-- Feed a fourth-moment estimate for a measurable Hilbert-`L²` family into
the ordinary probability-space `MemLp` interface. -/
theorem memLp_oneStepNormalizedFourthNormBorel_comp_of_moment
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {d : ℕ} (Q : TriadicCube d)
    (G : Omega → HilbertVectorL2 (openCubeSet Q)) (A : ℝ≥0∞)
    (hG : Measurable G)
    (hGfour : ∀ omega, MemLp (G omega : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q))
    (hA : A < ∞)
    (hmoment : ∫⁻ omega,
        (oneStepNormalizedFourthNormENNRealBorel Q (G omega)) ^ (4 : ℝ)
          ∂mu ≤ A ^ (4 : ℝ)) :
    MemLp (fun omega ↦ oneStepNormalizedFourthNormBorel Q (G omega)) 4 mu ∧
      eLpNorm (fun omega ↦ oneStepNormalizedFourthNormBorel Q (G omega))
        4 mu ≤ A := by
  simpa only [oneStepNormalizedFourthNormBorel] using!
    memLp_toReal_four_and_eLpNorm_le
      (fun omega ↦ oneStepNormalizedFourthNormENNRealBorel Q (G omega)) A
      ((measurable_oneStepNormalizedFourthNormENNRealBorel Q).comp hG)
      (fun omega ↦ by
        rw [oneStepNormalizedFourthNormENNRealBorel_eq_eLpNorm_coe]
        exact (hGfour omega).eLpNorm_ne_top)
      hA hmoment

theorem memLp_oneStepNormalizedFourthNormBorel_comp_of_raw_moment
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {d : ℕ} (Q : TriadicCube d)
    (G : Omega → HilbertVectorL2 (openCubeSet Q))
    (f : Omega → Vec d → HilbertVec d) (A : ℝ≥0∞)
    (hG : Measurable G)
    (hf : ∀ omega, MemLp (f omega) 4 (normalizedCubeMeasure Q))
    (hcoe : ∀ omega, (G omega : Vec d → HilbertVec d) =ᵐ[
      normalizedCubeMeasure Q] f omega)
    (hA : A < ∞)
    (hmoment : ∫⁻ omega,
        (eLpNorm (f omega) 4 (normalizedCubeMeasure Q)) ^ (4 : ℝ)
          ∂mu ≤ A ^ (4 : ℝ)) :
    MemLp (fun omega ↦ oneStepNormalizedFourthNormBorel Q (G omega)) 4 mu ∧
      eLpNorm (fun omega ↦ oneStepNormalizedFourthNormBorel Q (G omega))
        4 mu ≤ A := by
  apply memLp_oneStepNormalizedFourthNormBorel_comp_of_moment
    Q G A hG (fun omega ↦ (hf omega).ae_eq (hcoe omega).symm) hA
  calc
    _ = ∫⁻ omega,
        (eLpNorm (f omega) 4 (normalizedCubeMeasure Q)) ^ (4 : ℝ) ∂mu := by
      apply lintegral_congr
      intro omega
      rw [oneStepNormalizedFourthNormENNRealBorel_eq_eLpNorm_of_ae
        Q (G omega) (f omega) (hcoe omega)]
    _ ≤ _ := hmoment

private theorem integral_eq_toReal_eLpNorm_one_of_nonneg
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (f : Omega → ℝ) (hf : MemLp f 1 mu) (hf0 : ∀ omega, 0 ≤ f omega) :
    ∫ omega, f omega ∂mu = (eLpNorm f 1 mu).toReal := by
  rw [hf.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top]
  norm_num only [ENNReal.toReal_one, inv_one, Real.rpow_one,
    ENNReal.toReal_ofReal]
  rw [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)]
  exact integral_congr_ae <| Filter.Eventually.of_forall fun omega ↦ by
    change f omega = |f omega|
    rw [abs_of_nonneg (hf0 omega)]

theorem fourthRoot_mul_four_eq (C X : ℝ≥0∞) :
    (C * X ^ (4 : ℝ)) ^ (1 / 4 : ℝ) = C ^ (1 / 4 : ℝ) * X := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
  norm_num

/-- Probability-space Holder bound for the measurable four-norm envelope.
All four inputs are nonnegative; the output stays in exact `eLpNorm` form so
the model-specific fourth-moment constants can be inserted separately. -/
theorem integral_fourNormMajorant_le {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
    (U R Z E : Omega → ℝ)
    (hU0 : ∀ omega, 0 ≤ U omega) (hR0 : ∀ omega, 0 ≤ R omega)
    (hZ0 : ∀ omega, 0 ≤ Z omega) (hE0 : ∀ omega, 0 ≤ E omega)
    (hU : MemLp U 4 mu) (hR : MemLp R 4 mu)
    (hZ : MemLp Z 4 mu) (hE : MemLp E 4 mu) :
    Integrable (fun omega ↦ R omega * (2 * U omega + R omega) * Z omega +
        U omega * U omega * E omega) mu ∧
    ∫ omega, R omega * (2 * U omega + R omega) * Z omega +
        U omega * U omega * E omega ∂mu ≤
      (eLpNorm R 4 mu *
          (2 * eLpNorm U 4 mu + eLpNorm R 4 mu) * eLpNorm Z 4 mu).toReal +
        (eLpNorm U 4 mu * eLpNorm U 4 mu * eLpNorm E 4 mu).toReal := by
  let B : Omega → ℝ := fun omega ↦ 2 * U omega + R omega
  let first : Omega → ℝ := fun omega ↦ R omega * B omega * Z omega
  let second : Omega → ℝ := fun omega ↦ U omega * U omega * E omega
  have hB : MemLp B 4 mu := by
    exact (hU.const_mul 2).add hR
  have hB0 : ∀ omega, 0 ≤ B omega := fun omega ↦ by
    dsimp only [B]
    exact add_nonneg (mul_nonneg (by norm_num) (hU0 omega)) (hR0 omega)
  have hRfourMeas := hR.aestronglyMeasurable
  have hBfourMeas := hB.aestronglyMeasurable
  have hUfourMeas := hU.aestronglyMeasurable
  have hZfourMeas := hZ.aestronglyMeasurable
  have hEfourMeas := hE.aestronglyMeasurable
  have hRB : MemLp (fun omega ↦ R omega * B omega) 2 mu := by
    simpa only [Pi.mul_apply] using! hR.mul (r := 2) hB
  have hUU : MemLp (fun omega ↦ U omega * U omega) 2 mu := by
    simpa only [Pi.mul_apply] using! hU.mul (r := 2) hU
  have hZtwo : MemLp Z 2 mu := hZ.mono_exponent (by norm_num)
  have hEtwo : MemLp E 2 mu := hE.mono_exponent (by norm_num)
  have hfirst : MemLp first 1 mu := by
    simpa only [first, Pi.mul_apply] using! hRB.mul (r := 1) hZtwo
  have hsecond : MemLp second 1 mu := by
    simpa only [second, Pi.mul_apply] using! hUU.mul (r := 1) hEtwo
  have hBnorm : eLpNorm B 4 mu ≤ 2 * eLpNorm U 4 mu + eLpNorm R 4 mu := by
    have htri := eLpNorm_add_le (μ := mu) (f := fun omega ↦ 2 * U omega) (g := R)
      (by norm_num : (1 : ℝ≥0∞) ≤ 4)
    have hconst : eLpNorm (fun omega ↦ 2 * U omega) 4 mu ≤
        2 * eLpNorm U 4 mu := by
      have hfun : (2 : ℝ) • U = fun omega ↦ 2 * U omega := by
        funext omega
        simp [smul_eq_mul]
      rw [← hfun]
      convert (eLpNorm_const_smul_le (f := U) (p := (4 : ℝ≥0∞))
        (c := (2 : ℝ)) (μ := mu)) using 1
      norm_num [Real.enorm_eq_ofReal_abs]
    exact htri.trans (add_le_add hconst le_rfl)
  have hZnorm : eLpNorm Z 2 mu ≤ eLpNorm Z 4 mu := by
    simpa using! eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (f := Z) (μ := mu) (by norm_num : (2 : ℝ≥0∞) ≤ 4) hZ.aestronglyMeasurable
  have hEnorm : eLpNorm E 2 mu ≤ eLpNorm E 4 mu := by
    simpa using! eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (f := E) (μ := mu) (by norm_num : (2 : ℝ≥0∞) ≤ 4) hE.aestronglyMeasurable
  have hRBnorm : eLpNorm (fun omega ↦ R omega * B omega) 2 mu ≤
      eLpNorm R 4 mu * eLpNorm B 4 mu := by
    simpa using! eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (fun a b : ℝ ↦ a * b) 1 continuous_mul
      hRfourMeas hBfourMeas
      (Filter.Eventually.of_forall fun omega ↦ by simp)
  have hUUnorm : eLpNorm (fun omega ↦ U omega * U omega) 2 mu ≤
      eLpNorm U 4 mu * eLpNorm U 4 mu := by
    simpa using! eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (fun a b : ℝ ↦ a * b) 1 continuous_mul
      hUfourMeas hUfourMeas
      (Filter.Eventually.of_forall fun omega ↦ by simp)
  have hfirstNorm : eLpNorm first 1 mu ≤
      eLpNorm R 4 mu *
        (2 * eLpNorm U 4 mu + eLpNorm R 4 mu) * eLpNorm Z 4 mu := by
    have hprod : eLpNorm first 1 mu ≤
        eLpNorm (fun omega ↦ R omega * B omega) 2 mu * eLpNorm Z 2 mu := by
      simpa [first] using! eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
        (fun a b : ℝ ↦ a * b) 1 continuous_mul
        hRB.aestronglyMeasurable hZtwo.aestronglyMeasurable
        (Filter.Eventually.of_forall fun omega ↦ by simp)
    calc
      _ ≤ eLpNorm (fun omega ↦ R omega * B omega) 2 mu *
          eLpNorm Z 2 mu := hprod
      _ ≤ (eLpNorm R 4 mu * eLpNorm B 4 mu) * eLpNorm Z 2 mu := by
        gcongr
      _ ≤ eLpNorm R 4 mu *
          (2 * eLpNorm U 4 mu + eLpNorm R 4 mu) * eLpNorm Z 4 mu := by
        gcongr
  have hsecondNorm : eLpNorm second 1 mu ≤
      eLpNorm U 4 mu * eLpNorm U 4 mu * eLpNorm E 4 mu := by
    have hprod : eLpNorm second 1 mu ≤
        eLpNorm (fun omega ↦ U omega * U omega) 2 mu * eLpNorm E 2 mu := by
      simpa [second] using! eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
        (fun a b : ℝ ↦ a * b) 1 continuous_mul
        hUU.aestronglyMeasurable hEtwo.aestronglyMeasurable
        (Filter.Eventually.of_forall fun omega ↦ by simp)
    calc
      _ ≤ eLpNorm (fun omega ↦ U omega * U omega) 2 mu *
          eLpNorm E 2 mu := hprod
      _ ≤ (eLpNorm U 4 mu * eLpNorm U 4 mu) * eLpNorm E 2 mu := by
        gcongr
      _ ≤ eLpNorm U 4 mu * eLpNorm U 4 mu * eLpNorm E 4 mu := by
        gcongr
  refine ⟨by
    simpa only [first, second] using!
      (hfirst.integrable (by norm_num)).add (hsecond.integrable (by norm_num)), ?_⟩
  rw [show (∫ omega, R omega * (2 * U omega + R omega) * Z omega +
      U omega * U omega * E omega ∂mu) =
      ∫ omega, first omega + second omega ∂mu by rfl,
    integral_add (hfirst.integrable (by norm_num))
      (hsecond.integrable (by norm_num)),
    integral_eq_toReal_eLpNorm_one_of_nonneg first hfirst
      (fun omega ↦ by
        dsimp only [first, B]
        exact mul_nonneg (mul_nonneg (hR0 omega) (hB0 omega)) (hZ0 omega)),
    integral_eq_toReal_eLpNorm_one_of_nonneg second hsecond
      (fun omega ↦ by
        dsimp only [second]
        exact mul_nonneg (mul_nonneg (hU0 omega) (hU0 omega)) (hE0 omega))]
  exact add_le_add
    (ENNReal.toReal_mono
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hR.eLpNorm_ne_top
          (ENNReal.add_ne_top.mpr
            ⟨ENNReal.mul_ne_top (by norm_num) hU.eLpNorm_ne_top,
              hR.eLpNorm_ne_top⟩)) hZ.eLpNorm_ne_top)
      hfirstNorm)
    (ENNReal.toReal_mono
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hU.eLpNorm_ne_top hU.eLpNorm_ne_top)
        hE.eLpNorm_ne_top)
      hsecondNorm)

/-! ## Measurable residual solution families -/

theorem measurable_oneStepExpRemainderForcingL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (hh : 0 < h) :
    Measurable (oneStepExpRemainderForcingL2 M n h p Q) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  have hfull := measurable_oneStepShellForcingL2 M n h p Q hh
  have hlinear := measurable_oneStepLinearShellForcingL2 Q p n h
  have heq : oneStepExpRemainderForcingL2 M n h p Q =
      fun omega ↦ oneStepShellForcingL2 M n h p Q omega -
        oneStepLinearShellForcingL2 Q p n h omega := by
    funext omega
    rw [oneStepShellForcingL2_eq_linear_add_remainder M n h p Q omega hh]
    abel
  rw [heq]
  apply measurable_of_forall_real_inner_right
  intro Y
  have hfullY : Measurable fun omega ↦
      inner ℝ (oneStepShellForcingL2 M n h p Q omega) Y :=
    (continuous_id.inner continuous_const).measurable.comp hfull
  have hlinearY : Measurable fun omega ↦
      inner ℝ (oneStepLinearShellForcingL2 Q p n h omega) Y :=
    (continuous_id.inner continuous_const).measurable.comp hlinear
  simpa only [inner_sub_left] using! hfullY.sub hlinearY

theorem measurable_oneStepExpRemainderDirichletGradientL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable fun omega ↦
      (oneStepExpRemainderDirichletSolution M n h p m omega).toH1Function
        |>.gradToHilbertVectorL2 := by
  rw [funext fun omega ↦
    oneStepExpRemainderDirichletSolution_gradient_eq M n h p m omega]
  exact (continuous_oneStepDirichletGradientOfForcingClass
      (PotentialSolenoidalL2Data.ofSubmoduleClosures
        (openCubeSet (originCube d m)))
      (openCubeSet_nonempty_internal (originCube d m))
      (isEllipticFieldOn_identityCoeffField
        (measurableSet_openCubeSet (originCube d m)))).measurable.comp
    (measurable_oneStepExpRemainderForcingL2
      M n h p (originCube d m) hh).neg

theorem measurable_oneStepExpRemainderNeumannGradientL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable fun omega ↦
      (oneStepExpRemainderNeumannSolution M n h p m omega)
        |>.gradToHilbertVectorL2 := by
  rw [funext fun omega ↦
    oneStepExpRemainderNeumannSolution_gradient_eq M n h p m omega]
  exact (continuous_oneStepNeumannGradientOfForcingClass
      (translatedCubeMeanZeroH1CoerciveEstimate (originCube d m))
      (openCubeSet_nonempty_internal (originCube d m))
      (isEllipticFieldOn_identityCoeffField
        (measurableSet_openCubeSet (originCube d m)))).measurable.comp
    (measurable_oneStepExpRemainderForcingL2
      M n h p (originCube d m) hh).neg

/-- The literal normalized primal weighted-energy error on an origin cube. -/
def oneStepOriginDirichletWeightedCubicBorel {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  oneStepNormalizedWeightedCubicBorel (originCube d m) (HilbertVec.ofVec p)
    (oneStepOriginDirichletGradientL2 M n h p m omega)
    (oneStepShellForcingL2 M n h p (originCube d m) omega)

theorem measurable_oneStepOriginDirichletWeightedCubicBorel
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable (oneStepOriginDirichletWeightedCubicBorel M n h p m) := by
  let pair : _root_.SubdiffusiveProcess.Model.PotentialSample d →
      HilbertVectorL2 (openCubeSet (originCube d m)) ×
        HilbertVectorL2 (openCubeSet (originCube d m)) := fun omega ↦
    (oneStepOriginDirichletGradientL2 M n h p m omega,
      oneStepShellForcingL2 M n h p (originCube d m) omega)
  have hpair : Measurable pair :=
    (measurable_oneStepOriginDirichletGradientL2 M n h p m hh).prodMk
      (measurable_oneStepShellForcingL2 M n h p (originCube d m) hh)
  simpa only [oneStepOriginDirichletWeightedCubicBorel, pair] using!
    (measurable_oneStepNormalizedWeightedCubicBorel
      (originCube d m) (HilbertVec.ofVec p)).comp hpair

/-- The normalized primal odd cubic. -/
def oneStepNormalizedLinearDirichletCubicBorel {d : ℕ}
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  oneStepNormalizedWeightedCubicBorel Q (HilbertVec.ofVec p)
    (oneStepLinearDirichletGradient Q p n h omega)
    (oneStepLinearShellForcingL2 Q p n h omega)

theorem integral_oneStepNormalizedLinearDirichletCubicBorel_eq_zero
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) :
    ∫ omega, oneStepNormalizedLinearDirichletCubicBorel Q p n h omega
        ∂M.P.toMeasure = 0 := by
  have hmeas := measurable_oneStepLinearDirichletCubicBorel Q p n h
  change ∫ omega, (cubeVolume Q)⁻¹ *
      oneStepLinearDirichletCubicBorel Q p n h omega
      ∂M.P.toMeasure = 0
  rw [integral_const_mul,
    integral_oneStepLinearDirichletCubicBorel_eq_zero]
  ring

/-- Signed linear primal observable in the exact convention of the
nonlinear solution split `grad w = -grad v₀ + grad wbar`. -/
def oneStepNormalizedSignedLinearDirichletCubicBorel {d : ℕ}
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  oneStepNormalizedWeightedCubicBorel Q (HilbertVec.ofVec p)
    (-oneStepLinearDirichletGradient Q p n h omega)
    (oneStepLinearShellForcingL2 Q p n h omega)

theorem measurable_oneStepNormalizedSignedLinearDirichletCubicBorel
    {d : ℕ} (Q : TriadicCube d) (p : Vec d) (n h : ℕ) :
    Measurable (oneStepNormalizedSignedLinearDirichletCubicBorel Q p n h) := by
  let pair : _root_.SubdiffusiveProcess.Model.PotentialSample d →
      HilbertVectorL2 (openCubeSet Q) × HilbertVectorL2 (openCubeSet Q) :=
    fun omega ↦ (-oneStepLinearDirichletGradient Q p n h omega,
      oneStepLinearShellForcingL2 Q p n h omega)
  have hpair : Measurable pair :=
    (measurable_oneStepLinearDirichletGradient Q p n h).neg.prodMk
      (measurable_oneStepLinearShellForcingL2 Q p n h)
  simpa only [oneStepNormalizedSignedLinearDirichletCubicBorel, pair] using!
    (measurable_oneStepNormalizedWeightedCubicBorel Q
      (HilbertVec.ofVec p)).comp hpair

theorem oneStepNormalizedSignedLinearDirichletCubicBorel_negate
    {d : ℕ} (Q : TriadicCube d) (p : Vec d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    oneStepNormalizedSignedLinearDirichletCubicBorel Q p n h
        (negatePotentialSequence omega) =
      -oneStepNormalizedSignedLinearDirichletCubicBorel Q p n h omega := by
  unfold oneStepNormalizedSignedLinearDirichletCubicBorel
  rw [oneStepLinearDirichletGradient_negate,
    oneStepLinearShellForcingL2_negate]
  simp only [neg_neg]
  rw [oneStepNormalizedWeightedCubicBorel,
    oneStepNormalizedWeightedCubicBorel]
  have hcubic := oneStepWeightedCubicBorel_neg_neg
    (HilbertVec.ofVec p) (-oneStepLinearDirichletGradient Q p n h omega)
      (oneStepLinearShellForcingL2 Q p n h omega)
  simp only [neg_neg] at hcubic
  rw [hcubic]
  ring

theorem integral_oneStepNormalizedSignedLinearDirichletCubicBorel_eq_zero
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) :
    ∫ omega, oneStepNormalizedSignedLinearDirichletCubicBorel Q p n h omega
        ∂M.P.toMeasure = 0 := by
  exact integral_eq_zero_of_negatePotentialSequence_odd M
    (oneStepNormalizedSignedLinearDirichletCubicBorel Q p n h)
    (measurable_oneStepNormalizedSignedLinearDirichletCubicBorel Q p n h
      |>.aestronglyMeasurable)
    (oneStepNormalizedSignedLinearDirichletCubicBorel_negate Q p n h)

/-- The literal normalized reciprocal/Neumann weighted-energy error. -/
def oneStepOriginNeumannWeightedCubicBorel {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  oneStepNormalizedWeightedCubicBorel (originCube d m) (HilbertVec.ofVec p)
    (oneStepOriginNeumannGradientL2 M n h p m omega)
    (oneStepShellForcingL2 M n h p (originCube d m) omega)

theorem measurable_oneStepOriginNeumannWeightedCubicBorel
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable (oneStepOriginNeumannWeightedCubicBorel M n h p m) := by
  let pair : _root_.SubdiffusiveProcess.Model.PotentialSample d →
      HilbertVectorL2 (openCubeSet (originCube d m)) ×
        HilbertVectorL2 (openCubeSet (originCube d m)) := fun omega ↦
    (oneStepOriginNeumannGradientL2 M n h p m omega,
      oneStepShellForcingL2 M n h p (originCube d m) omega)
  have hpair : Measurable pair :=
    (measurable_oneStepOriginNeumannGradientL2 M n h p m hh).prodMk
      (measurable_oneStepShellForcingL2 M n h p (originCube d m) hh)
  simpa only [oneStepOriginNeumannWeightedCubicBorel, pair] using!
    (measurable_oneStepNormalizedWeightedCubicBorel
      (originCube d m) (HilbertVec.ofVec p)).comp hpair

/-- The normalized dual odd cubic. -/
def oneStepNormalizedLinearNeumannCubicBorel {d : ℕ}
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  oneStepNormalizedWeightedCubicBorel Q (HilbertVec.ofVec p)
    (oneStepLinearNeumannGradient Q p n h omega)
    (oneStepLinearShellForcingL2 Q p n h omega)

theorem integral_oneStepNormalizedLinearNeumannCubicBorel_eq_zero
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) :
    ∫ omega, oneStepNormalizedLinearNeumannCubicBorel Q p n h omega
        ∂M.P.toMeasure = 0 := by
  have hmeas := measurable_oneStepLinearNeumannCubicBorel Q p n h
  change ∫ omega, (cubeVolume Q)⁻¹ *
      oneStepLinearNeumannCubicBorel Q p n h omega
      ∂M.P.toMeasure = 0
  rw [integral_const_mul,
    integral_oneStepLinearNeumannCubicBorel_eq_zero]
  ring

/-- Signed Neumann linear observable matching the nonlinear split. -/
def oneStepNormalizedSignedLinearNeumannCubicBorel {d : ℕ}
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  oneStepNormalizedWeightedCubicBorel Q (HilbertVec.ofVec p)
    (-oneStepLinearNeumannGradient Q p n h omega)
    (oneStepLinearShellForcingL2 Q p n h omega)

theorem measurable_oneStepNormalizedSignedLinearNeumannCubicBorel
    {d : ℕ} (Q : TriadicCube d) (p : Vec d) (n h : ℕ) :
    Measurable (oneStepNormalizedSignedLinearNeumannCubicBorel Q p n h) := by
  let pair : _root_.SubdiffusiveProcess.Model.PotentialSample d →
      HilbertVectorL2 (openCubeSet Q) × HilbertVectorL2 (openCubeSet Q) :=
    fun omega ↦ (-oneStepLinearNeumannGradient Q p n h omega,
      oneStepLinearShellForcingL2 Q p n h omega)
  have hpair : Measurable pair :=
    (measurable_oneStepLinearNeumannGradient Q p n h).neg.prodMk
      (measurable_oneStepLinearShellForcingL2 Q p n h)
  simpa only [oneStepNormalizedSignedLinearNeumannCubicBorel, pair] using!
    (measurable_oneStepNormalizedWeightedCubicBorel Q
      (HilbertVec.ofVec p)).comp hpair

theorem oneStepNormalizedSignedLinearNeumannCubicBorel_negate
    {d : ℕ} (Q : TriadicCube d) (p : Vec d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    oneStepNormalizedSignedLinearNeumannCubicBorel Q p n h
        (negatePotentialSequence omega) =
      -oneStepNormalizedSignedLinearNeumannCubicBorel Q p n h omega := by
  unfold oneStepNormalizedSignedLinearNeumannCubicBorel
  rw [oneStepLinearNeumannGradient_negate,
    oneStepLinearShellForcingL2_negate]
  simp only [neg_neg]
  rw [oneStepNormalizedWeightedCubicBorel,
    oneStepNormalizedWeightedCubicBorel]
  have hcubic := oneStepWeightedCubicBorel_neg_neg
    (HilbertVec.ofVec p) (-oneStepLinearNeumannGradient Q p n h omega)
      (oneStepLinearShellForcingL2 Q p n h omega)
  simp only [neg_neg] at hcubic
  rw [hcubic]
  ring

theorem integral_oneStepNormalizedSignedLinearNeumannCubicBorel_eq_zero
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) :
    ∫ omega, oneStepNormalizedSignedLinearNeumannCubicBorel Q p n h omega
        ∂M.P.toMeasure = 0 := by
  exact integral_eq_zero_of_negatePotentialSequence_odd M
    (oneStepNormalizedSignedLinearNeumannCubicBorel Q p n h)
    (measurable_oneStepNormalizedSignedLinearNeumannCubicBorel Q p n h
      |>.aestronglyMeasurable)
    (oneStepNormalizedSignedLinearNeumannCubicBorel_negate Q p n h)

/-! ## Samplewise nonlinear-to-linear replacement -/

/-- The exact fourth-norm majorant produced by the primal replacement. -/
def oneStepOriginDirichletWeightedCubicMajorant {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  let Q := originCube d m
  let u := oneStepOriginDirichletGradientL2 M n h p m omega
  let v := -oneStepLinearDirichletGradient Q p n h omega
  let r := (oneStepExpRemainderDirichletSolution
    M n h p m omega).toH1Function.gradToHilbertVectorL2
  let z := oneStepLinearShellForcingL2 Q p n h omega
  let e := oneStepExpRemainderForcingL2 M n h p Q omega
  cubeLpNorm Q 4 (fun x ↦ ‖(r : Vec d → HilbertVec d) x‖) *
      cubeLpNorm Q 4 (fun x ↦
        ‖(u : Vec d → HilbertVec d) x‖ +
          ‖(v : Vec d → HilbertVec d) x‖) *
      cubeLpNorm Q 4 (fun x ↦ ‖(z : Vec d → HilbertVec d) x‖) +
    cubeLpNorm Q 4 (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖) *
      cubeLpNorm Q 4 (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖) *
      cubeLpNorm Q 4 (fun x ↦ ‖(e : Vec d → HilbertVec d) x‖)

/-- Measurable fourth-norm envelope for the primal replacement error. -/
def oneStepOriginDirichletWeightedCubicMajorantBorel {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  let Q := originCube d m
  let u := oneStepOriginDirichletGradientL2 M n h p m omega
  let r := (oneStepExpRemainderDirichletSolution
    M n h p m omega).toH1Function.gradToHilbertVectorL2
  let z := oneStepLinearShellForcingL2 Q p n h omega
  let e := oneStepExpRemainderForcingL2 M n h p Q omega
  oneStepNormalizedFourthNormBorel Q r *
      (2 * oneStepNormalizedFourthNormBorel Q u +
        oneStepNormalizedFourthNormBorel Q r) *
      oneStepNormalizedFourthNormBorel Q z +
    oneStepNormalizedFourthNormBorel Q u *
      oneStepNormalizedFourthNormBorel Q u *
      oneStepNormalizedFourthNormBorel Q e

theorem measurable_oneStepOriginDirichletWeightedCubicMajorantBorel
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable (oneStepOriginDirichletWeightedCubicMajorantBorel M n h p m) := by
  have hu := (measurable_oneStepNormalizedFourthNormBorel (originCube d m)).comp
    (measurable_oneStepOriginDirichletGradientL2 M n h p m hh)
  have hr := (measurable_oneStepNormalizedFourthNormBorel (originCube d m)).comp
    (measurable_oneStepExpRemainderDirichletGradientL2 M n h p m hh)
  have hz := (measurable_oneStepNormalizedFourthNormBorel (originCube d m)).comp
    (measurable_oneStepLinearShellForcingL2 (originCube d m) p n h)
  have he := (measurable_oneStepNormalizedFourthNormBorel (originCube d m)).comp
    (measurable_oneStepExpRemainderForcingL2
      M n h p (originCube d m) hh)
  exact ((hr.mul ((hu.const_mul 2).add hr)).mul hz).add
    ((hu.mul hu).mul he)

/-- The literal primal weighted-energy error differs from its odd linear
part by the fourth-norm majorant, sample by sample. -/
theorem abs_oneStepOriginDirichletWeightedCubicBorel_sub_linear_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    |oneStepOriginDirichletWeightedCubicBorel M n h p m omega -
      oneStepNormalizedSignedLinearDirichletCubicBorel
          (originCube d m) p n h omega| ≤
      oneStepOriginDirichletWeightedCubicMajorantBorel M n h p m omega := by
  let Q := originCube d m
  let u := oneStepOriginDirichletGradientL2 M n h p m omega
  let v := -oneStepLinearDirichletGradient Q p n h omega
  let r := (oneStepExpRemainderDirichletSolution
    M n h p m omega).toH1Function.gradToHilbertVectorL2
  let z := oneStepLinearShellForcingL2 Q p n h omega
  let e := oneStepExpRemainderForcingL2 M n h p Q omega
  obtain ⟨_Cactual, _hCactual, hCZactual⟩ :=
    exists_oneStepOriginDirichlet_gradient_four_cz d
  have hu4raw := (hCZactual M n h omega p m hh hp).1
  have hu4 : MemLp (u : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    have hmem := memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure Q
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function hu4raw
    rw [oneStepOriginDirichletSolution_gradient_eq M n h p m omega hh] at hmem
    exact hmem
  obtain ⟨_Crem, _hCrem, hCZrem⟩ :=
    exists_oneStepExpRemainderDirichlet_gradient_four_cz d
  have hr4raw := (hCZrem M n h omega p m hp).1
  have hr4 : MemLp (r : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    exact memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure Q
      (oneStepExpRemainderDirichletSolution M n h p m omega).toH1Function
      hr4raw
  have hz4 : MemLp (z : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    exact memLp_four_oneStepContinuousScalarForcingL2 Q p
      (oneStepShellSumContinuousMap n h omega)
  have he4 : MemLp (e : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    exact memLp_four_oneStepContinuousScalarForcingL2 Q p
      (oneStepExpRemainderContinuousMap M n h omega)
  have hsplit : u = v + r := by
    exact oneStepOriginDirichletGradientL2_eq_linear_add_remainder
      M n h p m omega hh
  have hvEq : v = u - r := by rw [hsplit]; abel
  have hsub : ((u - r : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (u : Vec d → HilbertVec d) - (r : Vec d → HilbertVec d) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    exact Lp.coeFn_sub u r
  have hv4 : MemLp (v : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    rw [hvEq]
    exact (hu4.sub hr4).ae_eq hsub.symm
  have hadd : ((v + r : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (v : Vec d → HilbertVec d) + (r : Vec d → HilbertVec d) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    exact Lp.coeFn_add v r
  have hu : (u : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (v : Vec d → HilbertVec d) + (r : Vec d → HilbertVec d) := by
    rw [hsplit]
    exact hadd
  have hpHilbert : ‖HilbertVec.ofVec p‖ ≤ 1 := by
    have hsquare : ‖HilbertVec.ofVec p‖ ^ 2 = 1 := by
      rw [HilbertVec.norm_sq_ofVec]
      exact hp
    nlinarith [norm_nonneg (HilbertVec.ofVec p)]
  have hdet : |oneStepOriginDirichletWeightedCubicBorel M n h p m omega -
      oneStepNormalizedSignedLinearDirichletCubicBorel
        (originCube d m) p n h omega| ≤
      oneStepOriginDirichletWeightedCubicMajorant M n h p m omega := by
    rw [oneStepOriginDirichletWeightedCubicBorel,
      oneStepShellForcingL2_eq_linear_add_remainder M n h p
        (originCube d m) omega hh]
    simpa only [
    oneStepNormalizedSignedLinearDirichletCubicBorel,
    oneStepOriginDirichletWeightedCubicMajorant, Q, u, v, r, z, e] using!
      abs_oneStepNormalizedWeightedCubicBorel_sub_le_four Q
        (HilbertVec.ofVec p) u v r z e hpHilbert hu hu4 hv4 hr4 hz4 he4
  exact hdet.trans (by
    simpa only [oneStepOriginDirichletWeightedCubicMajorant,
      oneStepOriginDirichletWeightedCubicMajorantBorel, Q, u, r, z, e] using!
      oneStepFourthNormMajorant_le_borel Q u v r z e hu hu4 hv4 hr4)

/-- The dual replacement majorant. -/
def oneStepOriginNeumannWeightedCubicMajorant {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  let Q := originCube d m
  let u := oneStepOriginNeumannGradientL2 M n h p m omega
  let v := -oneStepLinearNeumannGradient Q p n h omega
  let r := (oneStepExpRemainderNeumannSolution
    M n h p m omega).gradToHilbertVectorL2
  let z := oneStepLinearShellForcingL2 Q p n h omega
  let e := oneStepExpRemainderForcingL2 M n h p Q omega
  cubeLpNorm Q 4 (fun x ↦ ‖(r : Vec d → HilbertVec d) x‖) *
      cubeLpNorm Q 4 (fun x ↦
        ‖(u : Vec d → HilbertVec d) x‖ +
          ‖(v : Vec d → HilbertVec d) x‖) *
      cubeLpNorm Q 4 (fun x ↦ ‖(z : Vec d → HilbertVec d) x‖) +
    cubeLpNorm Q 4 (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖) *
      cubeLpNorm Q 4 (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖) *
      cubeLpNorm Q 4 (fun x ↦ ‖(e : Vec d → HilbertVec d) x‖)

/-- Measurable fourth-norm envelope for the dual replacement error. -/
def oneStepOriginNeumannWeightedCubicMajorantBorel {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  let Q := originCube d m
  let u := oneStepOriginNeumannGradientL2 M n h p m omega
  let r := (oneStepExpRemainderNeumannSolution
    M n h p m omega).gradToHilbertVectorL2
  let z := oneStepLinearShellForcingL2 Q p n h omega
  let e := oneStepExpRemainderForcingL2 M n h p Q omega
  oneStepNormalizedFourthNormBorel Q r *
      (2 * oneStepNormalizedFourthNormBorel Q u +
        oneStepNormalizedFourthNormBorel Q r) *
      oneStepNormalizedFourthNormBorel Q z +
    oneStepNormalizedFourthNormBorel Q u *
      oneStepNormalizedFourthNormBorel Q u *
      oneStepNormalizedFourthNormBorel Q e

theorem measurable_oneStepOriginNeumannWeightedCubicMajorantBorel
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable (oneStepOriginNeumannWeightedCubicMajorantBorel M n h p m) := by
  have hu := (measurable_oneStepNormalizedFourthNormBorel (originCube d m)).comp
    (measurable_oneStepOriginNeumannGradientL2 M n h p m hh)
  have hr := (measurable_oneStepNormalizedFourthNormBorel (originCube d m)).comp
    (measurable_oneStepExpRemainderNeumannGradientL2 M n h p m hh)
  have hz := (measurable_oneStepNormalizedFourthNormBorel (originCube d m)).comp
    (measurable_oneStepLinearShellForcingL2 (originCube d m) p n h)
  have he := (measurable_oneStepNormalizedFourthNormBorel (originCube d m)).comp
    (measurable_oneStepExpRemainderForcingL2
      M n h p (originCube d m) hh)
  exact ((hr.mul ((hu.const_mul 2).add hr)).mul hz).add
    ((hu.mul hu).mul he)

/-- Samplewise reciprocal/Neumann nonlinear-to-linear replacement. -/
theorem abs_oneStepOriginNeumannWeightedCubicBorel_sub_linear_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    |oneStepOriginNeumannWeightedCubicBorel M n h p m omega -
      oneStepNormalizedSignedLinearNeumannCubicBorel
          (originCube d m) p n h omega| ≤
      oneStepOriginNeumannWeightedCubicMajorantBorel M n h p m omega := by
  let Q := originCube d m
  let u := oneStepOriginNeumannGradientL2 M n h p m omega
  let v := -oneStepLinearNeumannGradient Q p n h omega
  let r := (oneStepExpRemainderNeumannSolution
    M n h p m omega).gradToHilbertVectorL2
  let z := oneStepLinearShellForcingL2 Q p n h omega
  let e := oneStepExpRemainderForcingL2 M n h p Q omega
  obtain ⟨_Cactual, _hCactual, hCZactual⟩ :=
    exists_oneStepOriginNeumann_gradient_four_cz d
  have hu4raw := (hCZactual M n h omega p m hh hp).1
  have hu4 : MemLp (u : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    have hmem := memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure Q
      (oneStepOriginNeumannSolution M n h p m omega hh).toH1Function hu4raw
    have hmem' : MemLp
        ((oneStepOriginNeumannSolution M n h p m omega hh).gradToHilbertVectorL2 :
          Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q) := by
      simpa only [H1MeanZeroFunction.gradToHilbertVectorL2] using! hmem
    rw [oneStepOriginNeumannSolution_gradient_eq M n h p m omega hh] at hmem'
    exact hmem'
  obtain ⟨_Crem, _hCrem, hCZrem⟩ :=
    exists_oneStepExpRemainderNeumann_gradient_four_cz d
  have hr4raw := (hCZrem M n h omega p m hp).1
  have hr4 : MemLp (r : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    exact memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure Q
      (oneStepExpRemainderNeumannSolution M n h p m omega).toH1Function
      hr4raw
  have hz4 : MemLp (z : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    exact memLp_four_oneStepContinuousScalarForcingL2 Q p
      (oneStepShellSumContinuousMap n h omega)
  have he4 : MemLp (e : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    exact memLp_four_oneStepContinuousScalarForcingL2 Q p
      (oneStepExpRemainderContinuousMap M n h omega)
  have hsplit : u = v + r := by
    exact oneStepOriginNeumannGradientL2_eq_linear_add_remainder
      M n h p m omega hh
  have hvEq : v = u - r := by rw [hsplit]; abel
  have hsub : ((u - r : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (u : Vec d → HilbertVec d) - (r : Vec d → HilbertVec d) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    exact Lp.coeFn_sub u r
  have hv4 : MemLp (v : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    rw [hvEq]
    exact (hu4.sub hr4).ae_eq hsub.symm
  have hadd : ((v + r : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (v : Vec d → HilbertVec d) + (r : Vec d → HilbertVec d) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    exact Lp.coeFn_add v r
  have hu : (u : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (v : Vec d → HilbertVec d) + (r : Vec d → HilbertVec d) := by
    rw [hsplit]
    exact hadd
  have hpHilbert : ‖HilbertVec.ofVec p‖ ≤ 1 := by
    have hsquare : ‖HilbertVec.ofVec p‖ ^ 2 = 1 := by
      rw [HilbertVec.norm_sq_ofVec]
      exact hp
    nlinarith [norm_nonneg (HilbertVec.ofVec p)]
  have hdet : |oneStepOriginNeumannWeightedCubicBorel M n h p m omega -
      oneStepNormalizedSignedLinearNeumannCubicBorel
        (originCube d m) p n h omega| ≤
      oneStepOriginNeumannWeightedCubicMajorant M n h p m omega := by
    rw [oneStepOriginNeumannWeightedCubicBorel,
      oneStepShellForcingL2_eq_linear_add_remainder M n h p
        (originCube d m) omega hh]
    simpa only [oneStepNormalizedSignedLinearNeumannCubicBorel,
      oneStepOriginNeumannWeightedCubicMajorant, Q, u, v, r, z, e] using!
      abs_oneStepNormalizedWeightedCubicBorel_sub_le_four Q
        (HilbertVec.ofVec p) u v r z e hpHilbert hu hu4 hv4 hr4 hz4 he4
  exact hdet.trans (by
    simpa only [oneStepOriginNeumannWeightedCubicMajorant,
      oneStepOriginNeumannWeightedCubicMajorantBorel, Q, u, r, z, e] using!
      oneStepFourthNormMajorant_le_borel Q u v r z e hu hu4 hv4 hr4)

/-- A normalized weighted cubic is controlled by two fourth norms of its
solution factor and one fourth norm of its forcing factor.  This is the
zero-comparator specialization of the nonlinear replacement inequality. -/
theorem abs_oneStepNormalizedWeightedCubicBorel_le_four
    {d : ℕ} (Q : TriadicCube d) (p : HilbertVec d)
    (u e : HilbertVectorL2 (openCubeSet Q))
    (hp : ‖p‖ ≤ 1)
    (hu4 : MemLp (u : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q))
    (he4 : MemLp (e : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q)) :
    |oneStepNormalizedWeightedCubicBorel Q p u e| ≤
      cubeLpNorm Q 4 (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖) *
        cubeLpNorm Q 4 (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖) *
        cubeLpNorm Q 4 (fun x ↦ ‖(e : Vec d → HilbertVec d) x‖) := by
  let z : HilbertVectorL2 (openCubeSet Q) := 0
  have hzAE : (z : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q] 0 :=
    ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q (by
      simpa only [z] using!
        Lp.coeFn_zero (HilbertVec d) (4 : ℝ≥0∞)
          (volumeMeasureOn (openCubeSet Q)))
  have hz4 : MemLp (z : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    exact MemLp.ae_eq hzAE.symm MemLp.zero
  have hu : (u : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (z : Vec d → HilbertVec d) + (u : Vec d → HilbertVec d) := by
    filter_upwards [hzAE] with x hx
    change (u : Vec d → HilbertVec d) x =
      (z : Vec d → HilbertVec d) x + (u : Vec d → HilbertVec d) x
    rw [hx]
    simp only [Pi.zero_apply, zero_add]
  have hzNormAE : (fun x ↦ ‖(z : Vec d → HilbertVec d) x‖) =ᵐ[
      normalizedCubeMeasure Q] 0 := by
    filter_upwards [hzAE] with x hx
    simp only [hx, Pi.zero_apply, norm_zero]
  have hzNorm : cubeLpNorm Q 4
      (fun x ↦ ‖(z : Vec d → HilbertVec d) x‖) = 0 := by
    unfold cubeLpNorm
    rw [eLpNorm_congr_ae hzNormAE]
    simp only [eLpNorm_zero, ENNReal.toReal_zero]
  have hzBorel : oneStepNormalizedWeightedCubicBorel Q p z z = 0 := by
    rw [oneStepNormalizedWeightedCubicBorel_eq_cubeAverage Q p z z hz4 hz4,
      cubeAverage_eq_integral_normalizedCubeMeasure]
    calc
      ∫ x, oneStepWeightedCubicIntegrand p z z x
          ∂normalizedCubeMeasure Q = ∫ _x, 0 ∂normalizedCubeMeasure Q :=
        integral_congr_ae (by
          filter_upwards [hzAE] with x hx
          unfold oneStepWeightedCubicIntegrand
          simp only [hx, Pi.zero_apply, norm_zero, inner_zero_right, mul_zero])
      _ = 0 := integral_zero _ _
  have h := abs_oneStepNormalizedWeightedCubicBorel_sub_le_four
    Q p u z u z e hp hu hu4 hz4 hu4 hz4 he4
  simpa only [z, zero_add, hzBorel, sub_zero, hzNorm, add_zero, mul_zero,
    zero_mul] using! h

/-- Fourth-norm domination of the literal primal weighted cubic by the
measurable component norms used in the probability-space closure. -/
theorem abs_oneStepOriginDirichletWeightedCubicBorel_le_components
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    |oneStepOriginDirichletWeightedCubicBorel M n h p m omega| ≤
      oneStepNormalizedFourthNormBorel (originCube d m)
          (oneStepOriginDirichletGradientL2 M n h p m omega) *
        oneStepNormalizedFourthNormBorel (originCube d m)
          (oneStepOriginDirichletGradientL2 M n h p m omega) *
        (oneStepNormalizedFourthNormBorel (originCube d m)
            (oneStepLinearShellForcingL2 (originCube d m) p n h omega) +
          oneStepNormalizedFourthNormBorel (originCube d m)
            (oneStepExpRemainderForcingL2 M n h p (originCube d m) omega)) := by
  let Q := originCube d m
  let u := oneStepOriginDirichletGradientL2 M n h p m omega
  let z := oneStepLinearShellForcingL2 Q p n h omega
  let e := oneStepExpRemainderForcingL2 M n h p Q omega
  let G := oneStepShellForcingL2 M n h p Q omega
  obtain ⟨_Cactual, _hCactual, hCZactual⟩ :=
    exists_oneStepOriginDirichlet_gradient_four_cz d
  have hu4raw := (hCZactual M n h omega p m hh hp).1
  have hu4 : MemLp (u : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    have hmem := memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure Q
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function hu4raw
    rw [oneStepOriginDirichletSolution_gradient_eq M n h p m omega hh] at hmem
    exact hmem
  have hz4 : MemLp (z : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) :=
    memLp_four_oneStepContinuousScalarForcingL2 Q p
      (oneStepShellSumContinuousMap n h omega)
  have he4 : MemLp (e : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) :=
    memLp_four_oneStepContinuousScalarForcingL2 Q p
      (oneStepExpRemainderContinuousMap M n h omega)
  have hG : G = z + e :=
    oneStepShellForcingL2_eq_linear_add_remainder M n h p Q omega hh
  have hadd : ((z + e : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (z : Vec d → HilbertVec d) + (e : Vec d → HilbertVec d) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    exact Lp.coeFn_add z e
  have hG4 : MemLp (G : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    rw [hG]
    exact (hz4.add he4).ae_eq hadd.symm
  have hpHilbert : ‖HilbertVec.ofVec p‖ ≤ 1 := by
    have hsquare : ‖HilbertVec.ofVec p‖ ^ 2 = 1 := by
      rw [HilbertVec.norm_sq_ofVec]
      exact hp
    nlinarith [norm_nonneg (HilbertVec.ofVec p)]
  have hraw := abs_oneStepNormalizedWeightedCubicBorel_le_four
    Q (HilbertVec.ofVec p) u G hpHilbert hu4 hG4
  have hGnorm : cubeLpNorm Q 4 (fun x ↦ ‖(G : Vec d → HilbertVec d) x‖) ≤
      cubeLpNorm Q 4 (fun x ↦ ‖(z : Vec d → HilbertVec d) x‖) +
        cubeLpNorm Q 4 (fun x ↦ ‖(e : Vec d → HilbertVec d) x‖) := by
    unfold cubeLpNorm
    rw [hG, eLpNorm_norm _ (weightedEnergy_aestronglyMeasurable_normalized Q (z + e)),
      eLpNorm_congr_ae hadd, eLpNorm_norm _ hz4.aestronglyMeasurable,
      eLpNorm_norm _ he4.aestronglyMeasurable]
    exact cubeLpNorm_add_le Q 4 (z : Vec d → HilbertVec d)
      (e : Vec d → HilbertVec d) hz4 he4 (by norm_num)
  have hbound := hraw.trans (mul_le_mul_of_nonneg_left hGnorm
    (mul_nonneg (cubeLpNorm_nonneg Q 4 _)
      (cubeLpNorm_nonneg Q 4 _)))
  simpa only [oneStepOriginDirichletWeightedCubicBorel, Q, u, z, e, G,
    oneStepNormalizedFourthNormBorel_eq_cubeLpNorm] using! hbound

/-- Reciprocal/Neumann counterpart of the componentwise cubic domination. -/
theorem abs_oneStepOriginNeumannWeightedCubicBorel_le_components
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    |oneStepOriginNeumannWeightedCubicBorel M n h p m omega| ≤
      oneStepNormalizedFourthNormBorel (originCube d m)
          (oneStepOriginNeumannGradientL2 M n h p m omega) *
        oneStepNormalizedFourthNormBorel (originCube d m)
          (oneStepOriginNeumannGradientL2 M n h p m omega) *
        (oneStepNormalizedFourthNormBorel (originCube d m)
            (oneStepLinearShellForcingL2 (originCube d m) p n h omega) +
          oneStepNormalizedFourthNormBorel (originCube d m)
            (oneStepExpRemainderForcingL2 M n h p (originCube d m) omega)) := by
  let Q := originCube d m
  let u := oneStepOriginNeumannGradientL2 M n h p m omega
  let z := oneStepLinearShellForcingL2 Q p n h omega
  let e := oneStepExpRemainderForcingL2 M n h p Q omega
  let G := oneStepShellForcingL2 M n h p Q omega
  obtain ⟨_Cactual, _hCactual, hCZactual⟩ :=
    exists_oneStepOriginNeumann_gradient_four_cz d
  have hu4raw := (hCZactual M n h omega p m hh hp).1
  have hu4 : MemLp (u : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    have hmem := memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure Q
      (oneStepOriginNeumannSolution M n h p m omega hh).toH1Function hu4raw
    have hmem' : MemLp
        ((oneStepOriginNeumannSolution M n h p m omega hh).gradToHilbertVectorL2 :
          Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q) := by
      simpa only [H1MeanZeroFunction.gradToHilbertVectorL2] using! hmem
    rw [oneStepOriginNeumannSolution_gradient_eq M n h p m omega hh] at hmem'
    exact hmem'
  have hz4 : MemLp (z : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) :=
    memLp_four_oneStepContinuousScalarForcingL2 Q p
      (oneStepShellSumContinuousMap n h omega)
  have he4 : MemLp (e : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) :=
    memLp_four_oneStepContinuousScalarForcingL2 Q p
      (oneStepExpRemainderContinuousMap M n h omega)
  have hG : G = z + e :=
    oneStepShellForcingL2_eq_linear_add_remainder M n h p Q omega hh
  have hadd : ((z + e : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (z : Vec d → HilbertVec d) + (e : Vec d → HilbertVec d) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    exact Lp.coeFn_add z e
  have hG4 : MemLp (G : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    rw [hG]
    exact (hz4.add he4).ae_eq hadd.symm
  have hpHilbert : ‖HilbertVec.ofVec p‖ ≤ 1 := by
    have hsquare : ‖HilbertVec.ofVec p‖ ^ 2 = 1 := by
      rw [HilbertVec.norm_sq_ofVec]
      exact hp
    nlinarith [norm_nonneg (HilbertVec.ofVec p)]
  have hraw := abs_oneStepNormalizedWeightedCubicBorel_le_four
    Q (HilbertVec.ofVec p) u G hpHilbert hu4 hG4
  have hGnorm : cubeLpNorm Q 4 (fun x ↦ ‖(G : Vec d → HilbertVec d) x‖) ≤
      cubeLpNorm Q 4 (fun x ↦ ‖(z : Vec d → HilbertVec d) x‖) +
        cubeLpNorm Q 4 (fun x ↦ ‖(e : Vec d → HilbertVec d) x‖) := by
    unfold cubeLpNorm
    rw [hG, eLpNorm_norm _ (weightedEnergy_aestronglyMeasurable_normalized Q (z + e)),
      eLpNorm_congr_ae hadd, eLpNorm_norm _ hz4.aestronglyMeasurable,
      eLpNorm_norm _ he4.aestronglyMeasurable]
    exact cubeLpNorm_add_le Q 4 (z : Vec d → HilbertVec d)
      (e : Vec d → HilbertVec d) hz4 he4 (by norm_num)
  have hbound := hraw.trans (mul_le_mul_of_nonneg_left hGnorm
    (mul_nonneg (cubeLpNorm_nonneg Q 4 _)
      (cubeLpNorm_nonneg Q 4 _)))
  simpa only [oneStepOriginNeumannWeightedCubicBorel, Q, u, z, e, G,
    oneStepNormalizedFourthNormBorel_eq_cubeLpNorm] using! hbound

/-! ## Probability fourth norms of the four canonical components -/

theorem exists_memLp_four_oneStepOriginDirichletFourthNorm
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (m : ℤ) (_hh : 0 < h) (_hp : vecNormSq p = 1),
        let A := (C *
          (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ)) ^
            (1 / 4 : ℝ)
        MemLp (fun omega ↦ oneStepNormalizedFourthNormBorel
            (originCube d m)
            (oneStepOriginDirichletGradientL2 M n h p m omega))
          4 M.P.toMeasure ∧
          eLpNorm (fun omega ↦ oneStepNormalizedFourthNormBorel
              (originCube d m)
              (oneStepOriginDirichletGradientL2 M n h p m omega))
            4 M.P.toMeasure ≤ A := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_lintegral_oneStepOriginDirichlet_gradient_four_le d
  obtain ⟨_Ccz, _hCcz, hCZ⟩ :=
    exists_oneStepOriginDirichlet_gradient_four_cz d
  refine ⟨C, hC, ?_⟩
  intro M n h p m hh hp
  let Q := originCube d m
  let G : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVectorL2 (openCubeSet Q) :=
    oneStepOriginDirichletGradientL2 M n h p m
  let f : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → HilbertVec d := fun omega ↦
    hilbertifyVecField
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad
  let A : ℝ≥0∞ := (C *
    (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ)) ^
      (1 / 4 : ℝ)
  have hf : ∀ omega, MemLp (f omega) 4 (normalizedCubeMeasure Q) := by
    intro omega
    simpa only [f, Q] using! (hCZ M n h omega p m hh hp).1
  have hcoe : ∀ omega, (G omega : Vec d → HilbertVec d) =ᵐ[
      normalizedCubeMeasure Q] f omega := by
    intro omega
    dsimp only [G, f, Q]
    rw [← oneStepOriginDirichletSolution_gradient_eq M n h p m omega hh]
    exact ae_normalizedCubeMeasure_of_ae_volumeMeasureOn _
      ((oneStepOriginDirichletSolution M n h p m omega hh).toH1Function
        |>.coeFn_gradToHilbertVectorL2)
  have hbaseTop : C *
      (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top hC.ne
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  have hAtop : A < ∞ := by
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hbaseTop
  have hA4 : A ^ (4 : ℝ) = C *
      (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
    dsimp only [A]
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
      ENNReal.rpow_inv_rpow (by norm_num)]
  have hm : ∫⁻ omega,
      (eLpNorm (f omega) 4 (normalizedCubeMeasure Q)) ^ (4 : ℝ)
        ∂M.P.toMeasure ≤ A ^ (4 : ℝ) := by
    have hraw : ∫⁻ omega,
        (eLpNorm (f omega) 4 (normalizedCubeMeasure Q)) ^ (4 : ℝ)
          ∂M.P.toMeasure ≤ C *
            (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^
              (4 : ℝ) := by
      simpa only [f, Q] using! hmoment M n h p m hh hp
    exact hraw.trans_eq hA4.symm
  simpa only [A, G, Q] using!
    memLp_oneStepNormalizedFourthNormBorel_comp_of_raw_moment
      Q G f A (measurable_oneStepOriginDirichletGradientL2 M n h p m hh)
      hf hcoe hAtop hm

theorem memLp_four_oneStepLinearShellFourthNorm
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1) :
    let A := oneStepLinearShellFourConst *
      ENNReal.ofReal (M.delta * Real.sqrt (h : ℝ))
    MemLp (fun omega ↦ oneStepNormalizedFourthNormBorel
        (originCube d m)
        (oneStepLinearShellForcingL2 (originCube d m) p n h omega))
      4 M.P.toMeasure ∧
      eLpNorm (fun omega ↦ oneStepNormalizedFourthNormBorel
          (originCube d m)
          (oneStepLinearShellForcingL2 (originCube d m) p n h omega))
        4 M.P.toMeasure ≤ A := by
  let Q := originCube d m
  let G : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVectorL2 (openCubeSet Q) :=
    oneStepLinearShellForcingL2 Q p n h
  let f : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → HilbertVec d := fun omega x ↦
    cutoffShellSum (n + h) (n : ℤ) x omega • HilbertVec.ofVec p
  let A : ℝ≥0∞ := oneStepLinearShellFourConst *
    ENNReal.ofReal (M.delta * Real.sqrt (h : ℝ))
  have hpNorm : ‖HilbertVec.ofVec p‖ = 1 := by
    have hsquare : ‖HilbertVec.ofVec p‖ ^ 2 = 1 := by
      rw [HilbertVec.norm_sq_ofVec]
      exact hp
    nlinarith [norm_nonneg (HilbertVec.ofVec p)]
  have hf : ∀ omega, MemLp (f omega) 4 (normalizedCubeMeasure Q) := by
    intro omega
    have hs : MemLp (fun x ↦ cutoffShellSum (n + h) (n : ℤ) x omega)
        4 (normalizedCubeMeasure Q) :=
      SubdiffusiveProcess.CoarseGrainingVocab.memLp_normalizedCubeMeasure_of_continuous
        Q 4 (oneStepShellSumContinuousMap n h omega).continuous
    let L : ℝ →L[ℝ] HilbertVec d :=
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (HilbertVec.ofVec p)
    simpa only [f, L, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self] using! hs.continuousLinearMap_comp L
  have hcoe : ∀ omega, (G omega : Vec d → HilbertVec d) =ᵐ[
      normalizedCubeMeasure Q] f omega := by
    intro omega
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    simpa only [G, f, oneStepLinearShellForcingL2,
      oneStepContinuousScalarForcingL2, oneStepShellSumContinuousMap] using!
      coeFn_toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepShellSumContinuousMap n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p)))
  have hAtop : A < ∞ := by
    exact lt_top_iff_ne_top.mpr <| ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top
  have hm : ∫⁻ omega,
      (eLpNorm (f omega) 4 (normalizedCubeMeasure Q)) ^ (4 : ℝ)
        ∂M.P.toMeasure ≤ A ^ (4 : ℝ) := by
    calc
      _ = ∫⁻ omega, ∫⁻ x,
          ‖cutoffShellSum (n + h) (n : ℤ) x omega‖ₑ ^ (4 : ℝ)
            ∂normalizedCubeMeasure Q ∂M.P.toMeasure := by
        apply lintegral_congr
        intro omega
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) ((hf omega).aestronglyMeasurable)]
        norm_num only [ENNReal.toReal_ofNat]
        rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
          ENNReal.rpow_inv_rpow (by norm_num)]
        apply lintegral_congr
        intro x
        have hpEnorm : ‖HilbertVec.ofVec p‖ₑ = 1 := by
          rw [← ofReal_norm, hpNorm]
          simp
        dsimp only [f]
        rw [enorm_smul, hpEnorm, mul_one]
      _ ≤ A ^ (4 : ℝ) := by
        simpa only [Q, A] using!
          lintegral_lintegral_cutoffShellSum_four_le M n h m hh
  simpa only [A, G, Q] using!
    memLp_oneStepNormalizedFourthNormBorel_comp_of_raw_moment
      Q G f A (measurable_oneStepLinearShellForcingL2 Q p n h)
      hf hcoe hAtop hm

theorem memLp_four_oneStepExpRemainderForcingFourthNorm
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    let A := oneStepExpRemainderConst *
      ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))
    MemLp (fun omega ↦ oneStepNormalizedFourthNormBorel
        (originCube d m)
        (oneStepExpRemainderForcingL2 M n h p (originCube d m) omega))
      4 M.P.toMeasure ∧
      eLpNorm (fun omega ↦ oneStepNormalizedFourthNormBorel
          (originCube d m)
          (oneStepExpRemainderForcingL2 M n h p (originCube d m) omega))
        4 M.P.toMeasure ≤ A := by
  let Q := originCube d m
  let G : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVectorL2 (openCubeSet Q) :=
    oneStepExpRemainderForcingL2 M n h p Q
  let f : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → HilbertVec d := fun omega x ↦
    oneStepExpRemainderAt M n h x omega • HilbertVec.ofVec p
  let A : ℝ≥0∞ := oneStepExpRemainderConst *
    ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))
  have hpNorm : ‖HilbertVec.ofVec p‖ = 1 := by
    have hsquare : ‖HilbertVec.ofVec p‖ ^ 2 = 1 := by
      rw [HilbertVec.norm_sq_ofVec]
      exact hp
    nlinarith [norm_nonneg (HilbertVec.ofVec p)]
  have hf : ∀ omega, MemLp (f omega) 4 (normalizedCubeMeasure Q) := by
    intro omega
    have hs := memLp_four_oneStepExpRemainderAt_spatial M n h m omega
    let L : ℝ →L[ℝ] HilbertVec d :=
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (HilbertVec.ofVec p)
    simpa only [f, L, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self] using! hs.continuousLinearMap_comp L
  have hcoe : ∀ omega, (G omega : Vec d → HilbertVec d) =ᵐ[
      normalizedCubeMeasure Q] f omega := by
    intro omega
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    simpa only [G, f, oneStepExpRemainderForcingL2,
      oneStepContinuousScalarForcingL2, oneStepExpRemainderContinuousMap] using!
      coeFn_toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepExpRemainderContinuousMap M n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p)))
  have hAtop : A < ∞ := by
    apply lt_top_iff_ne_top.mpr
    apply ENNReal.mul_ne_top
    · unfold oneStepExpRemainderConst
      finiteness
    · exact ENNReal.ofReal_ne_top
  have hm : ∫⁻ omega,
      (eLpNorm (f omega) 4 (normalizedCubeMeasure Q)) ^ (4 : ℝ)
        ∂M.P.toMeasure ≤ A ^ (4 : ℝ) := by
    calc
      _ = ∫⁻ omega, ∫⁻ x,
          ‖oneStepExpRemainderAt M n h x omega‖ₑ ^ (4 : ℝ)
            ∂normalizedCubeMeasure Q ∂M.P.toMeasure := by
        apply lintegral_congr
        intro omega
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) ((hf omega).aestronglyMeasurable)]
        norm_num only [ENNReal.toReal_ofNat]
        rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
          ENNReal.rpow_inv_rpow (by norm_num)]
        apply lintegral_congr
        intro x
        have hpEnorm : ‖HilbertVec.ofVec p‖ₑ = 1 := by
          rw [← ofReal_norm, hpNorm]
          simp
        dsimp only [f]
        rw [enorm_smul, hpEnorm, mul_one]
      _ ≤ A ^ (4 : ℝ) := by
        simpa only [Q, A] using!
          lintegral_lintegral_oneStepExpRemainder_four_le
            M n h m hh hscale
  simpa only [A, G, Q] using!
    memLp_oneStepNormalizedFourthNormBorel_comp_of_raw_moment
      Q G f A (measurable_oneStepExpRemainderForcingL2 M n h p Q hh)
      hf hcoe hAtop hm

theorem exists_memLp_four_oneStepExpRemainderDirichletFourthNorm
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (m : ℤ) (_hh : 0 < h) (_hp : vecNormSq p = 1)
        (_hscale : (h : ℝ) ≤ M.delta⁻¹),
        let A := (C * (oneStepExpRemainderConst *
          ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ)) ^
            (1 / 4 : ℝ)
        MemLp (fun omega ↦ oneStepNormalizedFourthNormBorel
            (originCube d m)
            ((oneStepExpRemainderDirichletSolution M n h p m omega)
              |>.toH1Function.gradToHilbertVectorL2))
          4 M.P.toMeasure ∧
          eLpNorm (fun omega ↦ oneStepNormalizedFourthNormBorel
              (originCube d m)
              ((oneStepExpRemainderDirichletSolution M n h p m omega)
                |>.toH1Function.gradToHilbertVectorL2))
            4 M.P.toMeasure ≤ A := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_lintegral_oneStepExpRemainderDirichlet_gradient_four_le d
  obtain ⟨_Ccz, _hCcz, hCZ⟩ :=
    exists_oneStepExpRemainderDirichlet_gradient_four_cz d
  refine ⟨C, hC, ?_⟩
  intro M n h p m hh hp hscale
  let Q := originCube d m
  let G : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVectorL2 (openCubeSet Q) := fun omega ↦
    (oneStepExpRemainderDirichletSolution M n h p m omega).toH1Function
      |>.gradToHilbertVectorL2
  let f : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → HilbertVec d := fun omega ↦
    hilbertifyVecField
      (oneStepExpRemainderDirichletSolution M n h p m omega).toH1Function.grad
  let A : ℝ≥0∞ := (C * (oneStepExpRemainderConst *
    ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ)) ^
      (1 / 4 : ℝ)
  have hf : ∀ omega, MemLp (f omega) 4 (normalizedCubeMeasure Q) := by
    intro omega
    simpa only [f, Q] using! (hCZ M n h omega p m hp).1
  have hcoe : ∀ omega, (G omega : Vec d → HilbertVec d) =ᵐ[
      normalizedCubeMeasure Q] f omega := by
    intro omega
    exact ae_normalizedCubeMeasure_of_ae_volumeMeasureOn _
      ((oneStepExpRemainderDirichletSolution M n h p m omega).toH1Function
        |>.coeFn_gradToHilbertVectorL2)
  have hbaseTop : C * (oneStepExpRemainderConst *
      ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ) ≠ ∞ := by
    apply ENNReal.mul_ne_top hC.ne
    apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    apply ENNReal.mul_ne_top
    · unfold oneStepExpRemainderConst
      finiteness
    · exact ENNReal.ofReal_ne_top
  have hAtop : A < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hbaseTop
  have hA4 : A ^ (4 : ℝ) = C * (oneStepExpRemainderConst *
      ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ) := by
    dsimp only [A]
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
      ENNReal.rpow_inv_rpow (by norm_num)]
  have hm : ∫⁻ omega,
      (eLpNorm (f omega) 4 (normalizedCubeMeasure Q)) ^ (4 : ℝ)
        ∂M.P.toMeasure ≤ A ^ (4 : ℝ) := by
    have hraw : ∫⁻ omega,
        (eLpNorm (f omega) 4 (normalizedCubeMeasure Q)) ^ (4 : ℝ)
          ∂M.P.toMeasure ≤ C * (oneStepExpRemainderConst *
            ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ) := by
      simpa only [f, Q] using! hmoment M n h p m hh hp hscale
    exact hraw.trans_eq hA4.symm
  simpa only [A, G, Q] using!
    memLp_oneStepNormalizedFourthNormBorel_comp_of_raw_moment
      Q G f A
      (measurable_oneStepExpRemainderDirichletGradientL2 M n h p m hh)
      hf hcoe hAtop hm

theorem exists_memLp_four_oneStepOriginNeumannFourthNorm
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (m : ℤ) (_hh : 0 < h) (_hp : vecNormSq p = 1),
        let A := (C *
          (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ)) ^
            (1 / 4 : ℝ)
        MemLp (fun omega ↦ oneStepNormalizedFourthNormBorel
            (originCube d m)
            (oneStepOriginNeumannGradientL2 M n h p m omega))
          4 M.P.toMeasure ∧
          eLpNorm (fun omega ↦ oneStepNormalizedFourthNormBorel
              (originCube d m)
              (oneStepOriginNeumannGradientL2 M n h p m omega))
            4 M.P.toMeasure ≤ A := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_lintegral_oneStepOriginNeumann_gradient_four_le d
  obtain ⟨_Ccz, _hCcz, hCZ⟩ :=
    exists_oneStepOriginNeumann_gradient_four_cz d
  refine ⟨C, hC, ?_⟩
  intro M n h p m hh hp
  let Q := originCube d m
  let G : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVectorL2 (openCubeSet Q) :=
    oneStepOriginNeumannGradientL2 M n h p m
  let f : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → HilbertVec d := fun omega ↦
    hilbertifyVecField
      (oneStepOriginNeumannSolution M n h p m omega hh).toH1Function.grad
  let A : ℝ≥0∞ := (C *
    (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ)) ^
      (1 / 4 : ℝ)
  have hf : ∀ omega, MemLp (f omega) 4 (normalizedCubeMeasure Q) := by
    intro omega
    simpa only [f, Q] using! (hCZ M n h omega p m hh hp).1
  have hcoe : ∀ omega, (G omega : Vec d → HilbertVec d) =ᵐ[
      normalizedCubeMeasure Q] f omega := by
    intro omega
    dsimp only [G, f, Q]
    rw [← oneStepOriginNeumannSolution_gradient_eq M n h p m omega hh]
    exact ae_normalizedCubeMeasure_of_ae_volumeMeasureOn _
      ((oneStepOriginNeumannSolution M n h p m omega hh).toH1Function
        |>.coeFn_gradToHilbertVectorL2)
  have hbaseTop : C *
      (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top hC.ne
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  have hAtop : A < ∞ := by
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hbaseTop
  have hA4 : A ^ (4 : ℝ) = C *
      (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
    dsimp only [A]
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
      ENNReal.rpow_inv_rpow (by norm_num)]
  have hm : ∫⁻ omega,
      (eLpNorm (f omega) 4 (normalizedCubeMeasure Q)) ^ (4 : ℝ)
        ∂M.P.toMeasure ≤ A ^ (4 : ℝ) := by
    have hraw : ∫⁻ omega,
        (eLpNorm (f omega) 4 (normalizedCubeMeasure Q)) ^ (4 : ℝ)
          ∂M.P.toMeasure ≤ C *
            (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^
              (4 : ℝ) := by
      simpa only [f, Q] using! hmoment M n h p m hh hp
    exact hraw.trans_eq hA4.symm
  simpa only [A, G, Q] using!
    memLp_oneStepNormalizedFourthNormBorel_comp_of_raw_moment
      Q G f A (measurable_oneStepOriginNeumannGradientL2 M n h p m hh)
      hf hcoe hAtop hm

theorem exists_memLp_four_oneStepExpRemainderNeumannFourthNorm
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (m : ℤ) (_hh : 0 < h) (_hp : vecNormSq p = 1)
        (_hscale : (h : ℝ) ≤ M.delta⁻¹),
        let A := (C * (oneStepExpRemainderConst *
          ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ)) ^
            (1 / 4 : ℝ)
        MemLp (fun omega ↦ oneStepNormalizedFourthNormBorel
            (originCube d m)
            ((oneStepExpRemainderNeumannSolution M n h p m omega)
              |>.gradToHilbertVectorL2))
          4 M.P.toMeasure ∧
          eLpNorm (fun omega ↦ oneStepNormalizedFourthNormBorel
              (originCube d m)
              ((oneStepExpRemainderNeumannSolution M n h p m omega)
                |>.gradToHilbertVectorL2))
            4 M.P.toMeasure ≤ A := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_lintegral_oneStepExpRemainderNeumann_gradient_four_le d
  obtain ⟨_Ccz, _hCcz, hCZ⟩ :=
    exists_oneStepExpRemainderNeumann_gradient_four_cz d
  refine ⟨C, hC, ?_⟩
  intro M n h p m hh hp hscale
  let Q := originCube d m
  let G : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVectorL2 (openCubeSet Q) := fun omega ↦
    (oneStepExpRemainderNeumannSolution M n h p m omega)
      |>.gradToHilbertVectorL2
  let f : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → HilbertVec d := fun omega ↦
    hilbertifyVecField
      (oneStepExpRemainderNeumannSolution M n h p m omega).toH1Function.grad
  let A : ℝ≥0∞ := (C * (oneStepExpRemainderConst *
    ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ)) ^
      (1 / 4 : ℝ)
  have hf : ∀ omega, MemLp (f omega) 4 (normalizedCubeMeasure Q) := by
    intro omega
    simpa only [f, Q] using! (hCZ M n h omega p m hp).1
  have hcoe : ∀ omega, (G omega : Vec d → HilbertVec d) =ᵐ[
      normalizedCubeMeasure Q] f omega := by
    intro omega
    exact ae_normalizedCubeMeasure_of_ae_volumeMeasureOn _
      ((oneStepExpRemainderNeumannSolution M n h p m omega).toH1Function
        |>.coeFn_gradToHilbertVectorL2)
  have hbaseTop : C * (oneStepExpRemainderConst *
      ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ) ≠ ∞ := by
    apply ENNReal.mul_ne_top hC.ne
    apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    apply ENNReal.mul_ne_top
    · unfold oneStepExpRemainderConst
      finiteness
    · exact ENNReal.ofReal_ne_top
  have hAtop : A < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hbaseTop
  have hA4 : A ^ (4 : ℝ) = C * (oneStepExpRemainderConst *
      ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ) := by
    dsimp only [A]
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
      ENNReal.rpow_inv_rpow (by norm_num)]
  have hm : ∫⁻ omega,
      (eLpNorm (f omega) 4 (normalizedCubeMeasure Q)) ^ (4 : ℝ)
        ∂M.P.toMeasure ≤ A ^ (4 : ℝ) := by
    have hraw : ∫⁻ omega,
        (eLpNorm (f omega) 4 (normalizedCubeMeasure Q)) ^ (4 : ℝ)
          ∂M.P.toMeasure ≤ C * (oneStepExpRemainderConst *
            ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ) := by
      simpa only [f, Q] using! hmoment M n h p m hh hp hscale
    exact hraw.trans_eq hA4.symm
  simpa only [A, G, Q] using!
    memLp_oneStepNormalizedFourthNormBorel_comp_of_raw_moment
      Q G f A
      (measurable_oneStepExpRemainderNeumannGradientL2 M n h p m hh)
      hf hcoe hAtop hm

/-! ## The cancelled weighted-energy expectations -/

theorem exists_integrable_oneStepOriginDirichletWeightedCubicMajorant
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (m : ℤ) (_ : 0 < h) (_ : vecNormSq p = 1)
        (_ : (h : ℝ) ≤ M.delta⁻¹),
        Integrable
          (oneStepOriginDirichletWeightedCubicMajorantBorel M n h p m)
          M.P.toMeasure ∧
        ∫ omega, oneStepOriginDirichletWeightedCubicMajorantBorel
            M n h p m omega ∂M.P.toMeasure ≤
          C * M.delta ^ 4 * (h : ℝ) ^ 2 := by
  obtain ⟨CD, hCDtop, hD⟩ :=
    exists_memLp_four_oneStepOriginDirichletFourthNorm d
  obtain ⟨CR, hCRtop, hR⟩ :=
    exists_memLp_four_oneStepExpRemainderDirichletFourthNorm d
  let KU : ℝ≥0∞ := CD ^ (1 / 4 : ℝ) *
    ENNReal.ofReal oneStepRatioEightUniformConst
  let KR : ℝ≥0∞ := CR ^ (1 / 4 : ℝ) * oneStepExpRemainderConst
  let KZ : ℝ≥0∞ := oneStepLinearShellFourConst
  let KE : ℝ≥0∞ := oneStepExpRemainderConst
  let K : ℝ≥0∞ := KR * (2 * KU + KR) * KZ + KU * KU * KE
  refine ⟨K.toReal + 1, by positivity, ?_⟩
  intro M n h p m hh hp hscale
  let Q := originCube d m
  let U : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepOriginDirichletGradientL2 M n h p m omega)
  let R : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    ((oneStepExpRemainderDirichletSolution M n h p m omega).toH1Function
      |>.gradToHilbertVectorL2)
  let Z : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepLinearShellForcingL2 Q p n h omega)
  let E : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepExpRemainderForcingL2 M n h p Q omega)
  obtain ⟨hUmem, hUnorm⟩ := hD M n h p m hh hp
  obtain ⟨hRmem, hRnorm⟩ := hR M n h p m hh hp hscale
  obtain ⟨hZmem, hZnorm⟩ :=
    memLp_four_oneStepLinearShellFourthNorm M n h p m hh hp
  obtain ⟨hEmem, hEnorm⟩ :=
    memLp_four_oneStepExpRemainderForcingFourthNorm
      M n h p m hh hp hscale
  have hU0 : ∀ omega, 0 ≤ U omega := fun _ ↦ ENNReal.toReal_nonneg
  have hR0 : ∀ omega, 0 ≤ R omega := fun _ ↦ ENNReal.toReal_nonneg
  have hZ0 : ∀ omega, 0 ≤ Z omega := fun _ ↦ ENNReal.toReal_nonneg
  have hE0 : ∀ omega, 0 ≤ E omega := fun _ ↦ ENNReal.toReal_nonneg
  have hagg := integral_fourNormMajorant_le U R Z E
    hU0 hR0 hZ0 hE0 hUmem hRmem hZmem hEmem
  have hratio := oneStepRatioMinusOneEightBound_le_sqrtScale M h hscale
  let x : ℝ := M.delta * Real.sqrt (h : ℝ)
  let y : ℝ := M.delta ^ 2 * (h : ℝ)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg M.shellPrefix.delta_pos.le (Real.sqrt_nonneg _)
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hyx : y = x ^ 2 := by
    dsimp [x, y]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg h)]
  have hx_le_one : x ≤ 1 := by
    have hdeltaSqH : M.delta ^ 2 * (h : ℝ) ≤ M.delta := by
      have hdh : M.delta * (h : ℝ) ≤ 1 := by
        calc
          M.delta * (h : ℝ) ≤ M.delta * M.delta⁻¹ :=
            mul_le_mul_of_nonneg_left hscale M.shellPrefix.delta_pos.le
          _ = 1 := mul_inv_cancel₀ M.shellPrefix.delta_pos.ne'
      nlinarith [M.shellPrefix.delta_pos]
    have hxSq : x ^ 2 ≤ 1 := by
      rw [← hyx]
      exact hdeltaSqH.trans M.shellPrefix.delta_le_half |>.trans (by norm_num)
    nlinarith
  have hy_le_x : y ≤ x := by rw [hyx]; nlinarith
  have hUenn : eLpNorm U 4 M.P.toMeasure ≤
      KU * ENNReal.ofReal x := by
    calc
      _ ≤ (CD * (ENNReal.ofReal
          (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ)) ^
            (1 / 4 : ℝ) := by simpa only [U, Q] using! hUnorm
      _ = CD ^ (1 / 4 : ℝ) *
          ENNReal.ofReal (oneStepRatioMinusOneEightBound M h) :=
        fourthRoot_mul_four_eq _ _
      _ ≤ KU * ENNReal.ofReal x := by
        dsimp only [KU, x]
        rw [mul_assoc]
        gcongr
        rw [← ENNReal.ofReal_mul oneStepRatioEightUniformConst_pos.le]
        exact ENNReal.ofReal_le_ofReal (by
          convert hratio using 1
          ring)
  have hRenn : eLpNorm R 4 M.P.toMeasure ≤
      KR * ENNReal.ofReal y := by
    calc
      _ ≤ (CR * (oneStepExpRemainderConst * ENNReal.ofReal y) ^
          (4 : ℝ)) ^ (1 / 4 : ℝ) := by
        simpa only [R, Q, y] using! hRnorm
      _ = CR ^ (1 / 4 : ℝ) *
          (oneStepExpRemainderConst * ENNReal.ofReal y) :=
        fourthRoot_mul_four_eq _ _
      _ = KR * ENNReal.ofReal y := by dsimp [KR]; ring
  have hZenn : eLpNorm Z 4 M.P.toMeasure ≤
      KZ * ENNReal.ofReal x := by
    simpa only [Z, Q, KZ, x] using! hZnorm
  have hEenn : eLpNorm E 4 M.P.toMeasure ≤
      KE * ENNReal.ofReal y := by
    simpa only [E, Q, KE, y] using! hEnorm
  have hKUtop : KU ≠ ∞ := by
    dsimp [KU]
    apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCDtop.ne
    · exact ENNReal.ofReal_ne_top
  have hKRtop : KR ≠ ∞ := by
    dsimp [KR]
    apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCRtop.ne
    · unfold oneStepExpRemainderConst
      finiteness
  have hKZtop : KZ ≠ ∞ := by dsimp [KZ, oneStepLinearShellFourConst]; finiteness
  have hKEtop : KE ≠ ∞ := by dsimp [KE, oneStepExpRemainderConst]; finiteness
  have hUreal : (eLpNorm U 4 M.P.toMeasure).toReal ≤ KU.toReal * x := by
    have := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hKUtop ENNReal.ofReal_ne_top) hUenn
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hx0] using! this
  have hRreal : (eLpNorm R 4 M.P.toMeasure).toReal ≤ KR.toReal * y := by
    have := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hKRtop ENNReal.ofReal_ne_top) hRenn
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hy0] using! this
  have hZreal : (eLpNorm Z 4 M.P.toMeasure).toReal ≤ KZ.toReal * x := by
    have := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hKZtop ENNReal.ofReal_ne_top) hZenn
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hx0] using! this
  have hEreal : (eLpNorm E 4 M.P.toMeasure).toReal ≤ KE.toReal * y := by
    have := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hKEtop ENNReal.ofReal_ne_top) hEenn
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hy0] using! this
  have hmid : 2 * (eLpNorm U 4 M.P.toMeasure).toReal +
      (eLpNorm R 4 M.P.toMeasure).toReal ≤
      (2 * KU.toReal + KR.toReal) * x := by
    have hRy : KR.toReal * y ≤ KR.toReal * x :=
      mul_le_mul_of_nonneg_left hy_le_x ENNReal.toReal_nonneg
    nlinarith
  have hboundReal :
      (eLpNorm R 4 M.P.toMeasure).toReal *
          (2 * (eLpNorm U 4 M.P.toMeasure).toReal +
            (eLpNorm R 4 M.P.toMeasure).toReal) *
          (eLpNorm Z 4 M.P.toMeasure).toReal +
        (eLpNorm U 4 M.P.toMeasure).toReal *
          (eLpNorm U 4 M.P.toMeasure).toReal *
          (eLpNorm E 4 M.P.toMeasure).toReal ≤ K.toReal * y ^ 2 := by
    have hprod1 := mul_le_mul
      (mul_le_mul hRreal hmid (by positivity) (by positivity)) hZreal
      (by positivity) (by positivity)
    have hprod2 := mul_le_mul
      (mul_le_mul hUreal hUreal (by positivity) (by positivity)) hEreal
      (by positivity) (by positivity)
    have hKreal : K.toReal =
        KR.toReal * (2 * KU.toReal + KR.toReal) * KZ.toReal +
          KU.toReal * KU.toReal * KE.toReal := by
      dsimp [K]
      rw [ENNReal.toReal_add
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top hKRtop
          (ENNReal.add_ne_top.mpr
            ⟨ENNReal.mul_ne_top (by norm_num) hKUtop, hKRtop⟩)) hKZtop)
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top hKUtop hKUtop) hKEtop)]
      simp only [ENNReal.toReal_mul]
      rw [ENNReal.toReal_add
        (ENNReal.mul_ne_top (by norm_num) hKUtop) hKRtop]
      norm_num
    have hprod1' :
        (eLpNorm R 4 M.P.toMeasure).toReal *
              (2 * (eLpNorm U 4 M.P.toMeasure).toReal +
                (eLpNorm R 4 M.P.toMeasure).toReal) *
              (eLpNorm Z 4 M.P.toMeasure).toReal ≤
            KR.toReal * (2 * KU.toReal + KR.toReal) * KZ.toReal * y ^ 2 := by
      calc
        _ ≤ KR.toReal * y * ((2 * KU.toReal + KR.toReal) * x) *
            (KZ.toReal * x) := hprod1
        _ = _ := by rw [hyx]; ring
    have hprod2' :
        (eLpNorm U 4 M.P.toMeasure).toReal *
              (eLpNorm U 4 M.P.toMeasure).toReal *
              (eLpNorm E 4 M.P.toMeasure).toReal ≤
            KU.toReal * KU.toReal * KE.toReal * y ^ 2 := by
      calc
        _ ≤ KU.toReal * x * (KU.toReal * x) * (KE.toReal * y) := hprod2
        _ = _ := by rw [hyx]; ring
    rw [hKreal]
    nlinarith
  have haggBound : ∫ omega,
      oneStepOriginDirichletWeightedCubicMajorantBorel M n h p m omega
        ∂M.P.toMeasure ≤ K.toReal * y ^ 2 := by
    have hmajorEq :
        (fun omega ↦ oneStepOriginDirichletWeightedCubicMajorantBorel
          M n h p m omega) =
        (fun omega ↦ R omega * (2 * U omega + R omega) * Z omega +
          U omega * U omega * E omega) := by
      rfl
    rw [hmajorEq]
    calc
      _ ≤ (eLpNorm R 4 M.P.toMeasure *
          (2 * eLpNorm U 4 M.P.toMeasure + eLpNorm R 4 M.P.toMeasure) *
          eLpNorm Z 4 M.P.toMeasure).toReal +
        (eLpNorm U 4 M.P.toMeasure * eLpNorm U 4 M.P.toMeasure *
          eLpNorm E 4 M.P.toMeasure).toReal := hagg.2
      _ = (eLpNorm R 4 M.P.toMeasure).toReal *
          (2 * (eLpNorm U 4 M.P.toMeasure).toReal +
            (eLpNorm R 4 M.P.toMeasure).toReal) *
          (eLpNorm Z 4 M.P.toMeasure).toReal +
        (eLpNorm U 4 M.P.toMeasure).toReal *
          (eLpNorm U 4 M.P.toMeasure).toReal *
          (eLpNorm E 4 M.P.toMeasure).toReal := by
        dsimp only [U, R, Z, E, Q]
        simp only [ENNReal.toReal_mul]
        rw [ENNReal.toReal_add
          (ENNReal.mul_ne_top (by norm_num) hUmem.eLpNorm_ne_top)
          hRmem.eLpNorm_ne_top]
        simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
      _ ≤ _ := hboundReal
  refine ⟨by
    simpa only [oneStepOriginDirichletWeightedCubicMajorantBorel,
      U, R, Z, E, Q] using! hagg.1, ?_⟩
  calc
    _ ≤ K.toReal * y ^ 2 := haggBound
    _ ≤ (K.toReal + 1) * M.delta ^ 4 * (h : ℝ) ^ 2 := by
      have hySq : y ^ 2 = M.delta ^ 4 * (h : ℝ) ^ 2 := by
        dsimp [y]
        ring
      rw [hySq]
      have hbase0 : 0 ≤ M.delta ^ 4 * (h : ℝ) ^ 2 := by positivity
      nlinarith [ENNReal.toReal_nonneg (a := K)]

/-- The probability-space Holder calculation underlying both nonlinear
weighted-energy replacement envelopes. -/
theorem integral_fourNormMajorant_quantitative
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (U R Z E : Omega → ℝ)
    (hU0 : ∀ omega, 0 ≤ U omega) (hR0 : ∀ omega, 0 ≤ R omega)
    (hZ0 : ∀ omega, 0 ≤ Z omega) (hE0 : ∀ omega, 0 ≤ E omega)
    (hUmem : MemLp U 4 mu) (hRmem : MemLp R 4 mu)
    (hZmem : MemLp Z 4 mu) (hEmem : MemLp E 4 mu)
    (KU KR KZ KE : ℝ≥0∞) (hKUtop : KU ≠ ∞) (hKRtop : KR ≠ ∞)
    (hKZtop : KZ ≠ ∞) (hKEtop : KE ≠ ∞)
    (x y : ℝ) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hyx : y = x ^ 2) (hy_le_x : y ≤ x)
    (hUenn : eLpNorm U 4 mu ≤ KU * ENNReal.ofReal x)
    (hRenn : eLpNorm R 4 mu ≤ KR * ENNReal.ofReal y)
    (hZenn : eLpNorm Z 4 mu ≤ KZ * ENNReal.ofReal x)
    (hEenn : eLpNorm E 4 mu ≤ KE * ENNReal.ofReal y) :
    let K : ℝ≥0∞ := KR * (2 * KU + KR) * KZ + KU * KU * KE
    Integrable (fun omega ↦
        R omega * (2 * U omega + R omega) * Z omega +
          U omega * U omega * E omega) mu ∧
      ∫ omega, R omega * (2 * U omega + R omega) * Z omega +
          U omega * U omega * E omega ∂mu ≤ K.toReal * y ^ 2 := by
  let K : ℝ≥0∞ := KR * (2 * KU + KR) * KZ + KU * KU * KE
  have hagg := integral_fourNormMajorant_le U R Z E
    hU0 hR0 hZ0 hE0 hUmem hRmem hZmem hEmem
  have hUreal : (eLpNorm U 4 mu).toReal ≤ KU.toReal * x := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hKUtop ENNReal.ofReal_ne_top) hUenn
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hx0] using! h
  have hRreal : (eLpNorm R 4 mu).toReal ≤ KR.toReal * y := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hKRtop ENNReal.ofReal_ne_top) hRenn
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hy0] using! h
  have hZreal : (eLpNorm Z 4 mu).toReal ≤ KZ.toReal * x := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hKZtop ENNReal.ofReal_ne_top) hZenn
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hx0] using! h
  have hEreal : (eLpNorm E 4 mu).toReal ≤ KE.toReal * y := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hKEtop ENNReal.ofReal_ne_top) hEenn
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hy0] using! h
  have hmid : 2 * (eLpNorm U 4 mu).toReal +
      (eLpNorm R 4 mu).toReal ≤ (2 * KU.toReal + KR.toReal) * x := by
    have hRy : KR.toReal * y ≤ KR.toReal * x :=
      mul_le_mul_of_nonneg_left hy_le_x ENNReal.toReal_nonneg
    nlinarith
  have hprod1 := mul_le_mul
    (mul_le_mul hRreal hmid (by positivity) (by positivity)) hZreal
    (by positivity) (by positivity)
  have hprod2 := mul_le_mul
    (mul_le_mul hUreal hUreal (by positivity) (by positivity)) hEreal
    (by positivity) (by positivity)
  have hKreal : K.toReal =
      KR.toReal * (2 * KU.toReal + KR.toReal) * KZ.toReal +
        KU.toReal * KU.toReal * KE.toReal := by
    dsimp [K]
    rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top hKRtop
        (ENNReal.add_ne_top.mpr
          ⟨ENNReal.mul_ne_top (by norm_num) hKUtop, hKRtop⟩)) hKZtop)
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top hKUtop hKUtop) hKEtop)]
    simp only [ENNReal.toReal_mul]
    rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top (by norm_num) hKUtop) hKRtop]
    norm_num
  have hprod1' :
      (eLpNorm R 4 mu).toReal *
            (2 * (eLpNorm U 4 mu).toReal + (eLpNorm R 4 mu).toReal) *
            (eLpNorm Z 4 mu).toReal ≤
          KR.toReal * (2 * KU.toReal + KR.toReal) * KZ.toReal * y ^ 2 := by
    calc
      _ ≤ KR.toReal * y * ((2 * KU.toReal + KR.toReal) * x) *
          (KZ.toReal * x) := hprod1
      _ = _ := by rw [hyx]; ring
  have hprod2' :
      (eLpNorm U 4 mu).toReal * (eLpNorm U 4 mu).toReal *
            (eLpNorm E 4 mu).toReal ≤
          KU.toReal * KU.toReal * KE.toReal * y ^ 2 := by
    calc
      _ ≤ KU.toReal * x * (KU.toReal * x) * (KE.toReal * y) := hprod2
      _ = _ := by rw [hyx]; ring
  refine ⟨hagg.1, hagg.2.trans ?_⟩
  simp only [ENNReal.toReal_mul]
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top (by norm_num) hUmem.eLpNorm_ne_top)
    hRmem.eLpNorm_ne_top, hKreal]
  norm_num
  calc
    _ ≤ KR.toReal * (2 * KU.toReal + KR.toReal) * KZ.toReal * y ^ 2 +
        KU.toReal * KU.toReal * KE.toReal * y ^ 2 :=
      add_le_add hprod1' hprod2'
    _ = _ := by ring

/-- Reciprocal/Neumann copy of the quantitative replacement envelope. -/
theorem exists_integrable_oneStepOriginNeumannWeightedCubicMajorant
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (m : ℤ) (_ : 0 < h) (_ : vecNormSq p = 1)
        (_ : (h : ℝ) ≤ M.delta⁻¹),
        Integrable
          (oneStepOriginNeumannWeightedCubicMajorantBorel M n h p m)
          M.P.toMeasure ∧
        ∫ omega, oneStepOriginNeumannWeightedCubicMajorantBorel
            M n h p m omega ∂M.P.toMeasure ≤
          C * M.delta ^ 4 * (h : ℝ) ^ 2 := by
  obtain ⟨CN, hCNtop, hN⟩ :=
    exists_memLp_four_oneStepOriginNeumannFourthNorm d
  obtain ⟨CR, hCRtop, hR⟩ :=
    exists_memLp_four_oneStepExpRemainderNeumannFourthNorm d
  let KU : ℝ≥0∞ := CN ^ (1 / 4 : ℝ) *
    ENNReal.ofReal oneStepRatioEightUniformConst
  let KR : ℝ≥0∞ := CR ^ (1 / 4 : ℝ) * oneStepExpRemainderConst
  let KZ : ℝ≥0∞ := oneStepLinearShellFourConst
  let KE : ℝ≥0∞ := oneStepExpRemainderConst
  let K : ℝ≥0∞ := KR * (2 * KU + KR) * KZ + KU * KU * KE
  refine ⟨K.toReal + 1, by positivity, ?_⟩
  intro M n h p m hh hp hscale
  let Q := originCube d m
  let U : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepOriginNeumannGradientL2 M n h p m omega)
  let R : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    ((oneStepExpRemainderNeumannSolution M n h p m omega)
      |>.gradToHilbertVectorL2)
  let Z : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepLinearShellForcingL2 Q p n h omega)
  let E : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepExpRemainderForcingL2 M n h p Q omega)
  obtain ⟨hUmem, hUnorm⟩ := hN M n h p m hh hp
  obtain ⟨hRmem, hRnorm⟩ := hR M n h p m hh hp hscale
  obtain ⟨hZmem, hZnorm⟩ :=
    memLp_four_oneStepLinearShellFourthNorm M n h p m hh hp
  obtain ⟨hEmem, hEnorm⟩ :=
    memLp_four_oneStepExpRemainderForcingFourthNorm M n h p m hh hp hscale
  let x : ℝ := M.delta * Real.sqrt (h : ℝ)
  let y : ℝ := M.delta ^ 2 * (h : ℝ)
  have hx0 : 0 ≤ x := mul_nonneg M.shellPrefix.delta_pos.le (Real.sqrt_nonneg _)
  have hy0 : 0 ≤ y := mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hyx : y = x ^ 2 := by
    dsimp [x, y]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg h)]
  have hx_le_one : x ≤ 1 := by
    have hdh : M.delta * (h : ℝ) ≤ 1 := by
      calc
        M.delta * (h : ℝ) ≤ M.delta * M.delta⁻¹ :=
          mul_le_mul_of_nonneg_left hscale M.shellPrefix.delta_pos.le
        _ = 1 := mul_inv_cancel₀ M.shellPrefix.delta_pos.ne'
    have hdeltaSqH : M.delta ^ 2 * (h : ℝ) ≤ M.delta := by
      nlinarith [M.shellPrefix.delta_pos]
    have hxSq : x ^ 2 ≤ 1 := by
      rw [← hyx]
      exact hdeltaSqH.trans M.shellPrefix.delta_le_half |>.trans (by norm_num)
    nlinarith
  have hy_le_x : y ≤ x := by rw [hyx]; nlinarith
  have hratio := oneStepRatioMinusOneEightBound_le_sqrtScale M h hscale
  have hUenn : eLpNorm U 4 M.P.toMeasure ≤ KU * ENNReal.ofReal x := by
    calc
      _ ≤ (CN * (ENNReal.ofReal
          (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ)) ^
            (1 / 4 : ℝ) := by simpa only [U, Q] using! hUnorm
      _ = CN ^ (1 / 4 : ℝ) *
          ENNReal.ofReal (oneStepRatioMinusOneEightBound M h) :=
        fourthRoot_mul_four_eq _ _
      _ ≤ KU * ENNReal.ofReal x := by
        dsimp only [KU, x]
        rw [mul_assoc]
        gcongr
        rw [← ENNReal.ofReal_mul oneStepRatioEightUniformConst_pos.le]
        exact ENNReal.ofReal_le_ofReal (by
          convert hratio using 1
          ring)
  have hRenn : eLpNorm R 4 M.P.toMeasure ≤ KR * ENNReal.ofReal y := by
    calc
      _ ≤ (CR * (oneStepExpRemainderConst * ENNReal.ofReal y) ^
          (4 : ℝ)) ^ (1 / 4 : ℝ) := by simpa only [R, Q, y] using! hRnorm
      _ = CR ^ (1 / 4 : ℝ) *
          (oneStepExpRemainderConst * ENNReal.ofReal y) :=
        fourthRoot_mul_four_eq _ _
      _ = KR * ENNReal.ofReal y := by dsimp [KR]; ring
  have hZenn : eLpNorm Z 4 M.P.toMeasure ≤ KZ * ENNReal.ofReal x := by
    simpa only [Z, Q, KZ, x] using! hZnorm
  have hEenn : eLpNorm E 4 M.P.toMeasure ≤ KE * ENNReal.ofReal y := by
    simpa only [E, Q, KE, y] using! hEnorm
  have hKUtop : KU ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCNtop.ne) ENNReal.ofReal_ne_top
  have hKRtop : KR ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCRtop.ne) (by
      unfold oneStepExpRemainderConst
      finiteness)
  have hKZtop : KZ ≠ ∞ := by dsimp [KZ, oneStepLinearShellFourConst]; finiteness
  have hKEtop : KE ≠ ∞ := by dsimp [KE, oneStepExpRemainderConst]; finiteness
  have hagg := integral_fourNormMajorant_quantitative M.P.toMeasure U R Z E
    (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ ENNReal.toReal_nonneg)
    (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ ENNReal.toReal_nonneg)
    hUmem hRmem hZmem hEmem KU KR KZ KE hKUtop hKRtop hKZtop hKEtop
    x y hx0 hy0 hyx hy_le_x hUenn hRenn hZenn hEenn
  refine ⟨by
    simpa only [oneStepOriginNeumannWeightedCubicMajorantBorel,
      U, R, Z, E, Q] using! hagg.1, ?_⟩
  calc
    _ ≤ K.toReal * y ^ 2 := by
      simpa only [oneStepOriginNeumannWeightedCubicMajorantBorel,
        U, R, Z, E, Q, K] using! hagg.2
    _ ≤ (K.toReal + 1) * M.delta ^ 4 * (h : ℝ) ^ 2 := by
      have hySq : y ^ 2 = M.delta ^ 4 * (h : ℝ) ^ 2 := by
        dsimp [y]
        ring
      rw [hySq]
      have hbase0 : 0 ≤ M.delta ^ 4 * (h : ℝ) ^ 2 := by positivity
      nlinarith [ENNReal.toReal_nonneg (a := K)]

/-! ## Cancellation and the literal weighted-energy expectations -/

theorem integrable_of_abs_le_fourProduct
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    (f U Z E : Omega → ℝ) (hf : AEStronglyMeasurable f mu)
    (hU : MemLp U 4 mu) (hZ : MemLp Z 4 mu) (hE : MemLp E 4 mu)
    (hbound : ∀ omega, |f omega| ≤ U omega * U omega * (Z omega + E omega))
    (hU0 : ∀ omega, 0 ≤ U omega) (hZ0 : ∀ omega, 0 ≤ Z omega)
    (hE0 : ∀ omega, 0 ≤ E omega) :
    Integrable f mu := by
  have hUU : MemLp (fun omega ↦ U omega * U omega) 2 mu := by
    simpa only [Pi.mul_apply] using! hU.mul (r := 2) hU
  have hZE : MemLp (fun omega ↦ Z omega + E omega) 2 mu :=
    (hZ.add hE).mono_exponent (by norm_num)
  have hprod : MemLp (fun omega ↦
      (U omega * U omega) * (Z omega + E omega)) 1 mu := by
    let : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) (1 : ℝ≥0∞) :=
      by infer_instance
    simpa only [Pi.mul_apply] using! hUU.mul (r := 1) hZE
  apply (hprod.integrable (by norm_num)).mono hf
  filter_upwards with omega
  have hnonneg : 0 ≤ U omega * U omega * (Z omega + E omega) :=
    mul_nonneg (mul_nonneg (hU0 omega) (hU0 omega))
      (add_nonneg (hZ0 omega) (hE0 omega))
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using! hbound omega

theorem abs_integral_of_cancelled_majorant
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (f linear majorant : Omega → ℝ)
    (hf : Integrable f mu) (hlinearMeas : AEStronglyMeasurable linear mu)
    (hlinearZero : ∫ omega, linear omega ∂mu = 0)
    (hmaj : Integrable majorant mu) (hmaj0 : ∀ omega, 0 ≤ majorant omega)
    (hpoint : ∀ omega, |f omega - linear omega| ≤ majorant omega)
    {B : ℝ} (hmajBound : ∫ omega, majorant omega ∂mu ≤ B) :
    |∫ omega, f omega ∂mu| ≤ B := by
  let difference : Omega → ℝ := fun omega ↦ f omega - linear omega
  have hdiffMeas : AEStronglyMeasurable difference mu :=
    hf.aestronglyMeasurable.sub hlinearMeas
  have hdiff : Integrable difference mu := by
    apply hmaj.mono hdiffMeas
    filter_upwards with omega
    simpa only [difference, Real.norm_eq_abs,
      abs_of_nonneg (hmaj0 omega)] using! hpoint omega
  have hlinear : Integrable linear mu := by
    have hsub := hf.sub hdiff
    have heq : f - difference = linear := by
      funext omega
      dsimp only [Pi.sub_apply, difference]
      ring
    rw [heq] at hsub
    exact hsub
  have hintegral : ∫ omega, f omega ∂mu =
      ∫ omega, difference omega ∂mu := by
    calc
      ∫ omega, f omega ∂mu =
          (∫ omega, f omega ∂mu) - ∫ omega, linear omega ∂mu := by
        rw [hlinearZero, sub_zero]
      _ = ∫ omega, difference omega ∂mu := by
        rw [← integral_sub hf hlinear]
  rw [hintegral]
  calc
    |∫ omega, difference omega ∂mu| ≤
        ∫ omega, |difference omega| ∂mu := abs_integral_le_integral_abs
    _ ≤ ∫ omega, majorant omega ∂mu := by
      apply integral_mono_ae hdiff.abs hmaj
      filter_upwards with omega
      exact hpoint omega
    _ ≤ B := hmajBound

/-- The literal primal nonlinear weighted term has the printed
`O(delta^4 h^2)` expectation after cancellation of its odd linear part. -/
theorem exists_integral_oneStepOriginDirichletWeightedCubicBorel_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (m : ℤ) (_ : 0 < h) (_ : vecNormSq p = 1)
        (_ : (h : ℝ) ≤ M.delta⁻¹),
        Integrable (oneStepOriginDirichletWeightedCubicBorel M n h p m)
            M.P.toMeasure ∧
          |∫ omega, oneStepOriginDirichletWeightedCubicBorel
              M n h p m omega ∂M.P.toMeasure| ≤
            C * M.delta ^ 4 * (h : ℝ) ^ 2 := by
  obtain ⟨C, hC, hmajor⟩ :=
    exists_integrable_oneStepOriginDirichletWeightedCubicMajorant d
  obtain ⟨_CD, _hCD, hD⟩ :=
    exists_memLp_four_oneStepOriginDirichletFourthNorm d
  refine ⟨C, hC, ?_⟩
  intro M n h p m hh hp hscale
  let Q := originCube d m
  let U : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepOriginDirichletGradientL2 M n h p m omega)
  let Z : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepLinearShellForcingL2 Q p n h omega)
  let E : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepExpRemainderForcingL2 M n h p Q omega)
  obtain ⟨hUmem, _hUnorm⟩ := hD M n h p m hh hp
  obtain ⟨hZmem, _hZnorm⟩ :=
    memLp_four_oneStepLinearShellFourthNorm M n h p m hh hp
  obtain ⟨hEmem, _hEnorm⟩ :=
    memLp_four_oneStepExpRemainderForcingFourthNorm M n h p m hh hp hscale
  obtain ⟨hmajInt, hmajBound⟩ := hmajor M n h p m hh hp hscale
  have hfInt : Integrable
      (oneStepOriginDirichletWeightedCubicBorel M n h p m) M.P.toMeasure :=
    integrable_of_abs_le_fourProduct
      (oneStepOriginDirichletWeightedCubicBorel M n h p m) U Z E
      (measurable_oneStepOriginDirichletWeightedCubicBorel M n h p m hh
        |>.aestronglyMeasurable)
      hUmem hZmem hEmem
      (fun omega ↦ by
        simpa only [U, Z, E, Q] using!
          abs_oneStepOriginDirichletWeightedCubicBorel_le_components
            M n h p m omega hh hp)
      (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ ENNReal.toReal_nonneg)
      (fun _ ↦ ENNReal.toReal_nonneg)
  refine ⟨hfInt, ?_⟩
  exact abs_integral_of_cancelled_majorant
    (oneStepOriginDirichletWeightedCubicBorel M n h p m)
    (oneStepNormalizedSignedLinearDirichletCubicBorel Q p n h)
    (oneStepOriginDirichletWeightedCubicMajorantBorel M n h p m)
    hfInt
    (measurable_oneStepNormalizedSignedLinearDirichletCubicBorel Q p n h
      |>.aestronglyMeasurable)
    (integral_oneStepNormalizedSignedLinearDirichletCubicBorel_eq_zero
      M Q p n h)
    hmajInt
    (fun omega ↦ by
      simp only [oneStepOriginDirichletWeightedCubicMajorantBorel]
      unfold oneStepNormalizedFourthNormBorel
      positivity)
    (fun omega ↦ abs_oneStepOriginDirichletWeightedCubicBorel_sub_linear_le
      M n h p m omega hh hp)
    hmajBound

/-- Neumann/reciprocal twin of the cancelled nonlinear weighted term. -/
theorem exists_integral_oneStepOriginNeumannWeightedCubicBorel_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (m : ℤ) (_ : 0 < h) (_ : vecNormSq p = 1)
        (_ : (h : ℝ) ≤ M.delta⁻¹),
        Integrable (oneStepOriginNeumannWeightedCubicBorel M n h p m)
            M.P.toMeasure ∧
          |∫ omega, oneStepOriginNeumannWeightedCubicBorel
              M n h p m omega ∂M.P.toMeasure| ≤
            C * M.delta ^ 4 * (h : ℝ) ^ 2 := by
  obtain ⟨C, hC, hmajor⟩ :=
    exists_integrable_oneStepOriginNeumannWeightedCubicMajorant d
  obtain ⟨_CN, _hCN, hN⟩ :=
    exists_memLp_four_oneStepOriginNeumannFourthNorm d
  refine ⟨C, hC, ?_⟩
  intro M n h p m hh hp hscale
  let Q := originCube d m
  let U : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepOriginNeumannGradientL2 M n h p m omega)
  let Z : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepLinearShellForcingL2 Q p n h omega)
  let E : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepExpRemainderForcingL2 M n h p Q omega)
  obtain ⟨hUmem, _hUnorm⟩ := hN M n h p m hh hp
  obtain ⟨hZmem, _hZnorm⟩ :=
    memLp_four_oneStepLinearShellFourthNorm M n h p m hh hp
  obtain ⟨hEmem, _hEnorm⟩ :=
    memLp_four_oneStepExpRemainderForcingFourthNorm M n h p m hh hp hscale
  obtain ⟨hmajInt, hmajBound⟩ := hmajor M n h p m hh hp hscale
  have hfInt : Integrable
      (oneStepOriginNeumannWeightedCubicBorel M n h p m) M.P.toMeasure :=
    integrable_of_abs_le_fourProduct
      (oneStepOriginNeumannWeightedCubicBorel M n h p m) U Z E
      (measurable_oneStepOriginNeumannWeightedCubicBorel M n h p m hh
        |>.aestronglyMeasurable)
      hUmem hZmem hEmem
      (fun omega ↦ by
        simpa only [U, Z, E, Q] using!
          abs_oneStepOriginNeumannWeightedCubicBorel_le_components
            M n h p m omega hh hp)
      (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ ENNReal.toReal_nonneg)
      (fun _ ↦ ENNReal.toReal_nonneg)
  refine ⟨hfInt, ?_⟩
  exact abs_integral_of_cancelled_majorant
    (oneStepOriginNeumannWeightedCubicBorel M n h p m)
    (oneStepNormalizedSignedLinearNeumannCubicBorel Q p n h)
    (oneStepOriginNeumannWeightedCubicMajorantBorel M n h p m)
    hfInt
    (measurable_oneStepNormalizedSignedLinearNeumannCubicBorel Q p n h
      |>.aestronglyMeasurable)
    (integral_oneStepNormalizedSignedLinearNeumannCubicBorel_eq_zero
      M Q p n h)
    hmajInt
    (fun omega ↦ by
      simp only [oneStepOriginNeumannWeightedCubicMajorantBorel]
      unfold oneStepNormalizedFourthNormBorel
      positivity)
    (fun omega ↦ abs_oneStepOriginNeumannWeightedCubicBorel_sub_linear_le
      M n h p m omega hh hp)
    hmajBound

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
