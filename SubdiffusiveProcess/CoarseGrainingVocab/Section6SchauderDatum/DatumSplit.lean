module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.Corrector


-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/OneStepDatumSplit.lean

@[expose] public section

/-!
# The datum reduction: from the true competitor to an odd one

The manuscript's boundary Schauder step reads

```text
  [∇v]_{C^{0,1/2}(U₃)} ≤ C 3^{-n/2} E(v, U₂)
                          + C [∇h]_{C^{0,1/2}(U₂)} 𝟙_{(x+□_n) ∩ ∂□_m ≠ ∅} .
```

The second leg is **not** a pricing of the odd-class defect; it lives in the
reduction from the true competitor `v` to an odd one `V_odd = v − ℓ_h − v₁`.
This module proves that reduction's two quantitative atoms.

## 1. The datum's deviation from its affine part

`Section6ExcessDecay.abs_sub_affineLift_volumeAverage_le` prices `h - ℓ_h` on a
convex window of sup-radius `r` by `2 d ([∇h] √d) r^{3/2}`.  Instantiated at
`U₂ = (x + □_{n-2}) ∩ □_m` and `r = 3^{n-2}/2` this is

```text
  ‖h - ℓ_h‖_{L^∞(U₂)} ≤ 2 d ([∇h]_{C^{0,1/2}(U₂)} √d) (3^{n-2}/2)^{3/2}
                      =: datumResidualBound d n [∇h] .
```

The integrability slot that lemma carries for the gradient field is **derived**
here, not assumed: a `C^{0,1/2}` field on a window is continuous
(`continuousOn_of_holderSeminormBoundOn`) and bounded, hence integrable.

## 2. The corrector carrying that deviation

`Corrector.exists_residualCorrector_truncatedWindow` solves the Dirichlet problem
on `U₂` with that datum and `MaxPrinciple.ae_abs_le_of_isUnitWeaklyHarmonicOn`
bounds the solution by the same constant.  The output `w` is the manuscript's
`v₁`:

```text
  v₁ weakly harmonic on U₂,  ‖v₁‖_{L^∞(U₂)} ≤ datumResidualBound d n [∇h] ,
```

with `v - ℓ_h - v₁` carrying **zero** data on the met portion of `∂□_m` — the odd
competitor `ZeroTrace` supplies to the proved reflection argument.

## 3. Where the `[∇h]` leg proves

The corrector is **not** priced through a gradient-Hölder seminorm: no interior
estimate reaches the met face, and a boundary Schauder estimate for `v₁` would be
circular.  It is priced through the `L̲²` comparison slot instead, and the
measured leg is

```text
  3^{-n} · datumResidualBound d n [∇h]
    = (2 d √d · 3^{-3} · 2^{-3/2}) (3^n)^{1/2} [∇h] ,
```

the manuscript's own `(3^n)^{1/2} [∇h]`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum

open MeasureTheory
open Homogenization (Vec H1Function MemH10 euclideanNorm volumeAverageVec volumeMeasureOn
  openCubeSet originCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ### A `C^{0,1/2}` field on a window is continuous and integrable -/

/-- **A Hölder field is continuous on its window.**  The `C^{0,1/2}` bound is an
explicit modulus of continuity; the ambient sup norm and the Euclidean magnitude
the seminorm is written in are comparable by the dimension. -/
theorem continuousOn_of_holderSeminormBoundOn {U : Set (Vec d)} {K : ℝ}
    {G : Vec d → Vec d} (hK : 0 ≤ K)
    (hG : HolderSeminormBoundOn U (1 / 2 : ℝ) K G) : ContinuousOn G U := by
  rw [Metric.continuousOn_iff]
  intro p hp ε hε
  have hK1 : (0 : ℝ) < K + 1 := by linarith only [hK]
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hquot : (0 : ℝ) < ε / (K + 1) := div_pos hε hK1
  refine ⟨(ε / (K + 1)) ^ 2 / ((d : ℝ) + 1), by positivity, ?_⟩
  intro q hq hdist
  have hnorm : ‖q - p‖ < (ε / (K + 1)) ^ 2 / ((d : ℝ) + 1) := by
    rwa [← dist_eq_norm]
  have hnn : (0 : ℝ) ≤ ‖q - p‖ := norm_nonneg _
  have heuc : euclideanNorm (q - p) ≤ (d : ℝ) * ‖q - p‖ :=
    Homogenization.euclideanNorm_le_dimension_mul_norm _
  have hsmall : euclideanNorm (q - p) ≤ (ε / (K + 1)) ^ 2 := by
    refine heuc.trans ?_
    have h1 : (d : ℝ) * ‖q - p‖ ≤ (d : ℝ) * ((ε / (K + 1)) ^ 2 / ((d : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hnorm.le (Nat.cast_nonneg d)
    refine h1.trans ?_
    rw [mul_div_assoc', div_le_iff₀ hd1]
    nlinarith only [hquot, hd1, sq_nonneg (ε / (K + 1))]
  have hroot : euclideanNorm (q - p) ^ (1 / 2 : ℝ) ≤ ((ε / (K + 1)) ^ 2) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (Homogenization.euclideanNorm_nonneg _) hsmall (by norm_num)
  have hcollapse : ((ε / (K + 1)) ^ 2) ^ (1 / 2 : ℝ) = ε / (K + 1) := by
    rw [← Real.rpow_natCast (ε / (K + 1)) 2, ← Real.rpow_mul hquot.le]
    norm_num
  rw [hcollapse] at hroot
  have hmain : ‖G q - G p‖ ≤ K * (ε / (K + 1)) := by
    refine le_trans (Homogenization.norm_le_euclideanNorm _) ?_
    exact le_trans (hG q hq p hp) (mul_le_mul_of_nonneg_left hroot hK)
  have hlt : K * (ε / (K + 1)) < ε := by
    rw [mul_div_assoc'] at hmain ⊢
    rw [div_lt_iff₀ hK1]
    linarith only [hε, hK]
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hmain hlt

/-- **A Hölder field is integrable on a bounded window**, coordinatewise.  This is
the integrability slot of
`Section6ExcessDecay.abs_sub_affineLift_volumeAverage_le`, and it is derived, not
assumed. -/
theorem integrableOn_coord_of_holderSeminormBoundOn {U : Set (Vec d)}
    (hU : MeasurableSet U) (hUtop : volume U ≠ ⊤) {K r : ℝ} {G : Vec d → Vec d}
    {x : Vec d} (hx : x ∈ U) (hK : 0 ≤ K)
    (hG : HolderSeminormBoundOn U (1 / 2 : ℝ) K G)
    (hdiam : ∀ p ∈ U, ‖p - x‖ ≤ r) (i : Fin d) :
    IntegrableOn (fun p => G p i) U volume := by
  have hr0 : (0 : ℝ) ≤ r := by
    have := hdiam x hx
    simpa using this
  have hcont : ContinuousOn G U := continuousOn_of_holderSeminormBoundOn hK hG
  have hcoord : ContinuousOn (fun p => G p i) U :=
    (continuous_apply i).comp_continuousOn hcont
  have hmeas : AEStronglyMeasurable (fun p => G p i) (volume.restrict U) :=
    hcoord.aestronglyMeasurable hU
  have : IsFiniteMeasure (volume.restrict U) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hUtop.lt_top
  refine memLp_one_iff_integrable.1
    (MemLp.of_bound hmeas (‖G x‖ + K * ((d : ℝ) * r) ^ (1 / 2 : ℝ)) ?_)
  filter_upwards [MeasureTheory.ae_restrict_mem hU] with p hp
  have hbase : euclideanNorm (p - x) ≤ (d : ℝ) * r :=
    (Homogenization.euclideanNorm_le_dimension_mul_norm _).trans
      (mul_le_mul_of_nonneg_left (hdiam p hp) (Nat.cast_nonneg d))
  have h1 : ‖G p - G x‖ ≤ K * ((d : ℝ) * r) ^ (1 / 2 : ℝ) := by
    refine le_trans (Homogenization.norm_le_euclideanNorm _) ?_
    refine le_trans (hG p hp x hx) (mul_le_mul_of_nonneg_left ?_ hK)
    exact Real.rpow_le_rpow (Homogenization.euclideanNorm_nonneg _) hbase (by norm_num)
  have h2 : ‖G p i‖ ≤ ‖G p‖ := by simpa using norm_le_pi_norm (G p) i
  have h3 : ‖G p‖ ≤ ‖G x‖ + ‖G p - G x‖ := by
    have := norm_add_le (G x) (G p - G x)
    simpa using this
  rw [Real.norm_eq_abs, ← Real.norm_eq_abs]
  linarith only [h1, h2, h3]

/-! ### The residual bound -/

/-- **The `L^∞` size of the datum's deviation from its affine lift on `U₂`**:
`2 d ([∇h] √d) (3^{n-2}/2)^{3/2}`. -/
def datumResidualBound (d : ℕ) (n : ℤ) (Kh : ℝ) : ℝ :=
  2 * (d : ℝ) * (Kh * Real.sqrt (d : ℝ)) * ((3 : ℝ) ^ (n - 2) / 2) ^ (3 / 2 : ℝ)

theorem datumResidualBound_nonneg (d : ℕ) (n : ℤ) {Kh : ℝ} (hKh : 0 ≤ Kh) :
    0 ≤ datumResidualBound d n Kh := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (n - 2) := zpow_pos (by norm_num) _
  have hr : (0 : ℝ) ≤ ((3 : ℝ) ^ (n - 2) / 2) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (by linarith only [h3]) _
  have hd : (0 : ℝ) ≤ 2 * (d : ℝ) * (Kh * Real.sqrt (d : ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
      (mul_nonneg hKh (Real.sqrt_nonneg _))
  exact mul_nonneg hd hr

/-- **The datum's deviation from its affine lift, on the boundary window.**  The
instantiation of `Section6ExcessDecay.abs_sub_affineLift_volumeAverage_le` at
`U₂ = (x + □_{n-2}) ∩ □_m` and sup-radius `3^{n-2}/2`, with the integrability
slot discharged. -/
theorem abs_sub_affineLift_le_truncatedWindow {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) {h : Vec d → ℝ} {G : Vec d → Vec d}
    {Kh : ℝ} (hKh : 0 ≤ Kh)
    (hgrad : HasGradientOn (truncatedWindow x m (n - 2)) h G)
    (hhol : HolderSeminormBoundOn (truncatedWindow x m (n - 2)) (1 / 2 : ℝ) Kh G)
    {y : Vec d} (hy : y ∈ truncatedWindow x m (n - 2)) :
    |h y - affineLift x (h x)
        (volumeAverageVec (truncatedWindow x m (n - 2)) G) y|
      ≤ datumResidualBound d n Kh := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (n - 2) := zpow_pos (by norm_num) _
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (n - 2) / 2 := by linarith only [h3]
  have hxU : x ∈ truncatedWindow x m (n - 2) := mem_truncatedWindow_self (n - 2) hx
  have hdiam : ∀ p ∈ truncatedWindow x m (n - 2), ‖p - x‖ ≤ (3 : ℝ) ^ (n - 2) / 2 :=
    fun p hp => norm_sub_le_of_mem_truncatedWindow hp
  have hint : ∀ i, IntegrableOn (fun p => G p i) (truncatedWindow x m (n - 2)) volume :=
    fun i => integrableOn_coord_of_holderSeminormBoundOn
      (isOpen_truncatedWindow x m (n - 2)).measurableSet
      (ne_of_lt (volume_truncatedWindow_lt_top x m (n - 2))) hxU hKh hhol hdiam i
  exact abs_sub_affineLift_volumeAverage_le
    (convex_truncatedWindow x m (n - 2)) hxU hy hKh hr0
    (volume_truncatedWindow_pos (n - 2) hx)
    (volume_truncatedWindow_lt_top x m (n - 2)) hint hgrad hhol hdiam

/-! ### The corrector carrying the datum's deviation -/

/-- **The datum corrector `v₁`.**

For an `H¹(U₂)` datum `Φ` bounded on `U₂` by `datumResidualBound d n Kh` — the
`H¹` realization of `h - ℓ_h`, whose bound §1 supplies — the Dirichlet problem on
`U₂` has a weakly harmonic solution `w` carrying `Φ`'s trace and satisfying the
same `L^∞` bound.  This is the manuscript's `v₁`; the two-sided weak maximum
principle is what turns the boundary datum's bound into the interior one. -/
theorem exists_datumCorrector [NeZero d] {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) {Kh : ℝ} (hKh : 0 ≤ Kh)
    (Φ : H1Function (truncatedWindow x m (n - 2)))
    (hΦ : ∀ y ∈ truncatedWindow x m (n - 2),
      |Φ.toFun y| ≤ datumResidualBound d n Kh) :
    ∃ w : H1Function (truncatedWindow x m (n - 2)),
      IsUnitWeaklyHarmonicOn (truncatedWindow x m (n - 2)) w ∧
      (∃ Ψ : H1Function (truncatedWindow x m (n - 2)),
        (∀ y ∈ truncatedWindow x m (n - 2), Ψ.toFun y = Φ.toFun y) ∧
        MemH10 (truncatedWindow x m (n - 2)) (fun y => w.toFun y - Ψ.toFun y)) ∧
      (∀ᵐ y ∂(volumeMeasureOn (truncatedWindow x m (n - 2))),
        |w.toFun y| ≤ datumResidualBound d n Kh) := by
  obtain ⟨Ψ, hub, hlb, hmatch⟩ :=
    exists_h1_clamp (isOpenBoundedConvexDomain_truncatedWindow x m (n - 2)) Φ
      (datumResidualBound_nonneg d n hKh)
  obtain ⟨w, hharm, hdiff, hbu, hbl⟩ :=
    exists_residualCorrector_truncatedWindow hx Ψ hub hlb
  exact ⟨w, hharm, ⟨Ψ, fun y hy => hmatch y (hΦ y hy), hdiff⟩,
    ae_abs_le_of_isUnitWeaklyHarmonicOn
      (isOpenBoundedConvexDomain_truncatedWindow x m (n - 2)) hharm hbu hbl⟩

/-! ### Where the `[∇h]` leg proves -/

/-- **The measured scale shape of the datum leg.**  The corrector enters the
one-step chain through the `L̲²` comparison slot, i.e. against the normalizer
`3^{-n}`; the product is the manuscript's own `(3^n)^{1/2} [∇h]`. -/
theorem datumResidualBound_zpow_mul (d : ℕ) (n : ℤ) (Kh : ℝ) :
    (3 : ℝ) ^ (-n) * datumResidualBound d n Kh
      = 2 * (d : ℝ) * (Kh * Real.sqrt (d : ℝ))
          * ((3 : ℝ) ^ (-3 : ℝ) * (2 : ℝ) ^ (-(3 / 2) : ℝ))
          * ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) := by
  have h3 : (0 : ℝ) < (3 : ℝ) := by norm_num
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos h3 _
  have hcast : ((3 : ℝ) ^ (n - 2)) = (3 : ℝ) ^ n * (3 : ℝ) ^ (-2 : ℤ) := by
    rw [← zpow_add₀ (ne_of_gt h3)]
    ring_nf
  have hsplit : ((3 : ℝ) ^ (n - 2) / 2) ^ (3 / 2 : ℝ)
      = ((3 : ℝ) ^ n) ^ (3 / 2 : ℝ) * (3 : ℝ) ^ (-3 : ℝ) * (2 : ℝ) ^ (-(3 / 2) : ℝ) := by
    have hpos2 : (0 : ℝ) < (3 : ℝ) ^ (-2 : ℤ) := zpow_pos h3 _
    rw [hcast, div_eq_mul_inv, Real.mul_rpow (mul_nonneg h3n.le hpos2.le) (by norm_num),
      Real.mul_rpow h3n.le hpos2.le]
    have hmid : ((3 : ℝ) ^ (-2 : ℤ)) ^ (3 / 2 : ℝ) = (3 : ℝ) ^ (-3 : ℝ) := by
      rw [show ((3 : ℝ) ^ (-2 : ℤ)) = (3 : ℝ) ^ ((-2 : ℝ)) by
        rw [show ((-2 : ℝ)) = (((-2 : ℤ) : ℝ)) by push_cast; ring, Real.rpow_intCast],
        ← Real.rpow_mul h3.le]
      norm_num
    have hinv : ((2 : ℝ)⁻¹) ^ (3 / 2 : ℝ) = (2 : ℝ) ^ (-(3 / 2) : ℝ) := by
      rw [← Real.rpow_neg_one (2 : ℝ), ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [hmid, hinv]
  have hthree : ((3 : ℝ) ^ n) ^ (3 / 2 : ℝ)
      = ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
    calc ((3 : ℝ) ^ n) ^ (3 / 2 : ℝ)
        = ((3 : ℝ) ^ n) ^ ((1 / 2 : ℝ) + 1) := by norm_num
      _ = ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) * ((3 : ℝ) ^ n) ^ (1 : ℝ) :=
          Real.rpow_add h3n _ _
      _ = ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) * (3 : ℝ) ^ n := by rw [Real.rpow_one]
  have hcancel : (3 : ℝ) ^ (-n) * (3 : ℝ) ^ n = 1 := by
    rw [← zpow_add₀ (ne_of_gt h3)]
    simp
  rw [datumResidualBound, hsplit, hthree]
  calc (3 : ℝ) ^ (-n) * (2 * (d : ℝ) * (Kh * Real.sqrt (d : ℝ))
        * (((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) * (3 : ℝ) ^ n * (3 : ℝ) ^ (-3 : ℝ)
          * (2 : ℝ) ^ (-(3 / 2) : ℝ)))
      = ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ n) * (2 * (d : ℝ) * (Kh * Real.sqrt (d : ℝ))
          * ((3 : ℝ) ^ (-3 : ℝ) * (2 : ℝ) ^ (-(3 / 2) : ℝ))
          * ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ)) := by ring
    _ = 2 * (d : ℝ) * (Kh * Real.sqrt (d : ℝ))
          * ((3 : ℝ) ^ (-3 : ℝ) * (2 : ℝ) ^ (-(3 / 2) : ℝ))
          * ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) := by rw [hcancel, one_mul]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum
