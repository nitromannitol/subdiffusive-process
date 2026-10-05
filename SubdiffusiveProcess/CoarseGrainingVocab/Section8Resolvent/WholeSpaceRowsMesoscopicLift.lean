module

public import SubdiffusiveProcess.CoarseGrainingVocab.CaccioppoliRHS
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsForcedBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsMesoscopicSplit
public import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.OverlapPoincare
public import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.StandardOverlapComparison

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open Homogenization.Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The geometric ratio of the depth series -/

/-- The ratio of the geometric series summed by the positive-Besov gradient
estimate: the depth-`j` contribution to the *squared* seminorm decays like
`(3 ^ (2(s-1)))ᶨ`.  Finiteness of the series is exactly `s < 1`. -/
def besovGradientRatio (s : ℝ) : ℝ :=
  Real.rpow (3 : ℝ) (2 * (s - 1))

theorem besovGradientRatio_pos (s : ℝ) : 0 < besovGradientRatio s :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem besovGradientRatio_lt_one {s : ℝ} (hs : s < 1) :
    besovGradientRatio s < 1 := by
  have : (2 : ℝ) * (s - 1) < 0 := by nlinarith
  simpa [besovGradientRatio] using
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) this

theorem one_sub_besovGradientRatio_pos {s : ℝ} (hs : s < 1) :
    0 < 1 - besovGradientRatio s := by
  have := besovGradientRatio_lt_one hs
  linarith

/-- The dimension- and exponent-only constant of the positive-Besov gradient
estimate. -/
def besovH1GradientConstant (d : ℕ) (s : ℝ) : ℝ :=
  Real.sqrt ((3 : ℝ) ^ d) * cubeVectorH1OverlapPoincareConstant d /
    Real.sqrt (1 - besovGradientRatio s)

theorem besovH1GradientConstant_nonneg (d : ℕ) (s : ℝ) :
    0 ≤ besovH1GradientConstant d s := by
  unfold besovH1GradientConstant
  exact div_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (cubeVectorH1OverlapPoincareConstant_nonneg d))
    (Real.sqrt_nonneg _)

/-! ## The depth estimate -/

/-- **The depth-`j` positive Besov seminorm of a coordinatewise `H¹` vector
field decays geometrically.**

The non-overlapping depth average is comparable to the overlapping one
(`cubeBesovPositiveVectorDepthAverage_le_three_pow_mul_overlapping`), and the
overlapping one obeys the scale-correct Poincaré inequality
`cubeVectorH1OverlapPoincareEstimate`, which carries the single factor `3^{-j}`
(the side of a depth-`j` descendant, relative to the parent).  The weight
`3^{s j}` of the positive seminorm then leaves `3^{(s-1)j}`. -/
theorem cubeBesovPositiveVectorDepthSeminorm_toField_le
    (Q : TriadicCube d) (G : CubeVectorH1Function Q) (s : ℝ) (j : ℕ) :
    cubeBesovPositiveVectorDepthSeminorm Q s G.toField j ≤
      Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) *
        (Real.sqrt ((3 : ℝ) ^ d) * cubeVectorH1OverlapPoincareConstant d *
          G.relativeGradientCoordL2NormSum) := by
  classical
  set A : ℝ := cubeBesovPositiveVectorDepthAverage Q G.toField j with hAdef
  set Aov : ℝ := cubeBesovOverlappingPositiveVectorDepthAverage Q G.toField j
    with hAovdef
  have hcmp : A ≤ (3 ^ d : ℝ) * Aov :=
    cubeBesovPositiveVectorDepthAverage_le_three_pow_mul_overlapping Q G.toField j
  have hsqrt_cmp : Real.sqrt A ≤ Real.sqrt ((3 : ℝ) ^ d) * Real.sqrt Aov := by
    calc
      Real.sqrt A ≤ Real.sqrt ((3 ^ d : ℝ) * Aov) := Real.sqrt_le_sqrt hcmp
      _ = Real.sqrt ((3 : ℝ) ^ d) * Real.sqrt Aov :=
        Real.sqrt_mul (by positivity) _
  have hpoin : Real.sqrt Aov ≤
      cubeVectorH1OverlapPoincareConstant d * Real.rpow (3 : ℝ) (-(j : ℝ)) *
        G.relativeGradientCoordL2NormSum :=
    cubeVectorH1OverlapPoincareEstimate d Q j G
  have hweight_nonneg : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (s * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsqrt3d : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ d) := Real.sqrt_nonneg _
  have hstep : Real.sqrt A ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        (cubeVectorH1OverlapPoincareConstant d * Real.rpow (3 : ℝ) (-(j : ℝ)) *
          G.relativeGradientCoordL2NormSum) :=
    hsqrt_cmp.trans (mul_le_mul_of_nonneg_left hpoin hsqrt3d)
  have hmul :
      Real.rpow (3 : ℝ) (s * (j : ℝ)) * Real.rpow (3 : ℝ) (-(j : ℝ)) =
        Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) := by
    have h := Real.rpow_add (show (0 : ℝ) < 3 by norm_num) (s * (j : ℝ)) (-(j : ℝ))
    have he : s * (j : ℝ) + -(j : ℝ) = (s - 1) * (j : ℝ) := by ring
    rw [he] at h
    exact h.symm
  calc
    cubeBesovPositiveVectorDepthSeminorm Q s G.toField j
        = Real.rpow (3 : ℝ) (s * (j : ℝ)) * Real.sqrt A := rfl
    _ ≤ Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          (Real.sqrt ((3 : ℝ) ^ d) *
            (cubeVectorH1OverlapPoincareConstant d *
              Real.rpow (3 : ℝ) (-(j : ℝ)) *
              G.relativeGradientCoordL2NormSum)) :=
        mul_le_mul_of_nonneg_left hstep hweight_nonneg
    _ = (Real.rpow (3 : ℝ) (s * (j : ℝ)) * Real.rpow (3 : ℝ) (-(j : ℝ))) *
          (Real.sqrt ((3 : ℝ) ^ d) * cubeVectorH1OverlapPoincareConstant d *
            G.relativeGradientCoordL2NormSum) := by ring
    _ = Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) *
          (Real.sqrt ((3 : ℝ) ^ d) * cubeVectorH1OverlapPoincareConstant d *
            G.relativeGradientCoordL2NormSum) := by rw [hmul]

/-- The squared depth weight is the `j`-th power of the geometric ratio. -/
theorem sq_rpow_three_eq_besovGradientRatio_pow (s : ℝ) (j : ℕ) :
    (Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))) ^ 2 = (besovGradientRatio s) ^ j := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hL : Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) *
      Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) =
      Real.rpow (3 : ℝ) (2 * (s - 1) * (j : ℝ)) := by
    have h := (Real.rpow_add h3 ((s - 1) * (j : ℝ)) ((s - 1) * (j : ℝ))).symm
    have he : (s - 1) * (j : ℝ) + (s - 1) * (j : ℝ) = 2 * (s - 1) * (j : ℝ) := by
      ring
    rw [he] at h
    exact h
  have hR : Real.rpow (3 : ℝ) (2 * (s - 1) * (j : ℝ)) =
      (besovGradientRatio s) ^ j := by
    have h := Real.rpow_mul h3.le (2 * (s - 1)) (j : ℝ)
    have h2 := Real.rpow_natCast (Real.rpow (3 : ℝ) (2 * (s - 1))) j
    unfold besovGradientRatio
    exact h.trans h2
  rw [sq, hL, hR]

/-- The finite geometric series, bounded by its sum. -/
theorem sum_geometric_le_inv_one_sub {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    (∑ j ∈ Finset.range n, q ^ j) ≤ (1 - q)⁻¹ := by
  have hsummable : Summable fun j : ℕ => q ^ j := summable_geometric_of_lt_one hq0 hq1
  have hle := hsummable.sum_le_tsum (Finset.range n)
    (fun j _ => pow_nonneg hq0 j)
  rwa [tsum_geometric_of_lt_one hq0 hq1] at hle

/-! ## The positive Besov seminorm of a coordinatewise `H¹` field -/

/-- **The positive Besov seminorm of a coordinatewise `H¹` vector field is
controlled by its scale-normalized gradient**, uniformly in the truncation
depth.  Valid for every `s < 1`; the constant blows up as `s → 1`, which is the
divergence of the geometric series `Σ 3^{2(s-1)j}`. -/
theorem cubeBesovPositiveVectorPartialSeminormTwo_toField_le
    (Q : TriadicCube d) (G : CubeVectorH1Function Q) {s : ℝ} (hs : s < 1) (N : ℕ) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N G.toField ≤
      besovH1GradientConstant d s * G.relativeGradientCoordL2NormSum := by
  classical
  set K : ℝ := Real.sqrt ((3 : ℝ) ^ d) * cubeVectorH1OverlapPoincareConstant d *
    G.relativeGradientCoordL2NormSum with hKdef
  have hK0 : 0 ≤ K := by
    refine mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) ?_) ?_
    · exact cubeVectorH1OverlapPoincareConstant_nonneg d
    · exact G.relativeGradientCoordL2NormSum_nonneg
  set q : ℝ := besovGradientRatio s with hqdef
  have hq0 : 0 ≤ q := (besovGradientRatio_pos s).le
  have hq1 : q < 1 := besovGradientRatio_lt_one hs
  have hone_sub : 0 < 1 - q := by linarith
  set B : ℝ := besovH1GradientConstant d s * G.relativeGradientCoordL2NormSum with hBdef
  have hB0 : 0 ≤ B :=
    mul_nonneg (besovH1GradientConstant_nonneg d s)
      G.relativeGradientCoordL2NormSum_nonneg
  have hBsq : B ^ 2 = K ^ 2 / (1 - q) := by
    have hsqrt : Real.sqrt (1 - q) ^ 2 = 1 - q := Real.sq_sqrt hone_sub.le
    have hBK : B = K / Real.sqrt (1 - q) := by
      rw [hBdef, hKdef, besovH1GradientConstant, hqdef]
      ring
    rw [hBK, div_pow, hsqrt]
  have hterm : ∀ j ∈ Finset.range (N + 1),
      (cubeBesovPositiveVectorDepthSeminorm Q s G.toField j) ^ 2 ≤ q ^ j * K ^ 2 := by
    intro j _
    have hd0 : 0 ≤ cubeBesovPositiveVectorDepthSeminorm Q s G.toField j :=
      cubeBesovPositiveVectorDepthSeminorm_nonneg Q s G.toField j
    have hle := cubeBesovPositiveVectorDepthSeminorm_toField_le Q G s j
    have hrhs0 : 0 ≤ Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) * K :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) hK0
    calc
      (cubeBesovPositiveVectorDepthSeminorm Q s G.toField j) ^ 2
          ≤ (Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) * K) ^ 2 := by
            exact pow_le_pow_left₀ hd0 hle 2
      _ = (Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))) ^ 2 * K ^ 2 := by ring
      _ = q ^ j * K ^ 2 := by rw [sq_rpow_three_eq_besovGradientRatio_pow]
  have hsum :
      (cubeBesovPositiveVectorPartialSeminormTwo Q s N G.toField) ^ 2 ≤ B ^ 2 := by
    rw [sq_cubeBesovPositiveVectorPartialSeminormTwo, hBsq]
    calc
      (∑ j ∈ Finset.range (N + 1),
          (cubeBesovPositiveVectorDepthSeminorm Q s G.toField j) ^ 2)
          ≤ ∑ j ∈ Finset.range (N + 1), q ^ j * K ^ 2 :=
            Finset.sum_le_sum hterm
      _ = (∑ j ∈ Finset.range (N + 1), q ^ j) * K ^ 2 := by
            rw [Finset.sum_mul]
      _ ≤ (1 - q)⁻¹ * K ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (sum_geometric_le_inv_one_sub hq0 hq1 (N + 1)) (sq_nonneg K)
      _ = K ^ 2 / (1 - q) := by field_simp
  have hP0 : 0 ≤ cubeBesovPositiveVectorPartialSeminormTwo Q s N G.toField :=
    cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s N G.toField
  nlinarith [hsum, hP0, hB0]

/-- The full note-normalized positive Besov seminorm of a coordinatewise `H¹`
vector field: `[F]_{B^{s,+}(Q)} ≤ C(d,s) · side(Q) · ‖∇F‖_{L̲²(Q)}`. -/
theorem scaleNormalizedPositiveBesovVectorSeminormTwo_toField_le
    (Q : TriadicCube d) (G : CubeVectorH1Function Q) {s : ℝ} (hs : s < 1) :
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s G.toField ≤
      besovH1GradientConstant d s * G.relativeGradientCoordL2NormSum :=
  cubeBesovPositiveVectorSeminormTwo_le_of_partialBound Q s G.toField
    fun N => cubeBesovPositiveVectorPartialSeminormTwo_toField_le Q G hs N

/-- A coordinatewise `H¹` vector field is an admissible Chapter 3 forcing datum
at every positive order `s < 1`. -/
theorem forceBesovRegularity_toField
    (Q : TriadicCube d) (G : CubeVectorH1Function Q) {s : ℝ} (hs : s < 1) :
    Ch03.ForceBesovRegularity Q s G.toField where
  memLp := G.memLp_toField_normalizedCubeMeasure
  partialSeminorms_bddAbove := by
    refine ⟨besovH1GradientConstant d s * G.relativeGradientCoordL2NormSum, ?_⟩
    rintro x ⟨N, rfl⟩
    exact cubeBesovPositiveVectorPartialSeminormTwo_toField_le Q G hs N

/-! ## The mesoscopic lift -/



theorem exists_mesoscopic_forced_datum (d : ℕ) [NeZero d] {s : ℝ} (hs : s < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : TriadicCube d) (afam : Ch03.CoeffFamily d) (a : Vec d → ℝ),
        (∀ x, (afam.coeffOn Q).toCoeffField x = scalarCoeffField a x) →
        ∀ (mu : ℝ) (u : H1Function (openCubeSet Q)),
          IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu (openCubeSet Q) u
            (fun _ ↦ (0 : ℝ)) →
          ∃ g : Vec d → Vec d,
            Ch03.IsForcedEquation Q afam u g ∧
            Ch03.ForceBesovRegularity Q s g ∧
            Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s g ≤
              C * (cubeScaleFactor Q *
                (|mu| * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun)) := by
  classical
  obtain ⟨Clift, hClift0, hlift⟩ := exists_cubeVectorH1Function_divergence_lift d
  refine ⟨besovH1GradientConstant d s * Clift,
    mul_nonneg (besovH1GradientConstant_nonneg d s) hClift0, ?_⟩
  intro Q afam a hA mu u hu
  have hmem : MemLp (fun x ↦ mu * u.toFun x) 2 (volume.restrict (openCubeSet Q)) :=
    u.memL2.const_mul mu
  obtain ⟨F, hpair, hnorm⟩ := hlift Q (fun x ↦ mu * u.toFun x) hmem
  refine ⟨F.toField, ?_, forceBesovRegularity_toField Q F hs, ?_⟩
  · intro phi
    have heq := hu phi
    simp only [one_mul, zero_mul, integral_zero] at heq
    have hmass :
        (∫ x in openCubeSet Q, (fun y ↦ mu * u.toFun y) x *
            phi.toH1Function.toFun x ∂volume) =
          mu * ∫ x in openCubeSet Q, u.toFun x * phi.toH1Function.toFun x
            ∂volume := by
      simp_rw [mul_assoc]
      exact integral_const_mul _ _
    have hlhs :
        (∫ x in openCubeSet Q,
            vecDot (matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x))
              (phi.toH1Function.grad x) ∂volume) =
          ∫ x in openCubeSet Q,
            vecDot (a x • u.grad x) (phi.toH1Function.grad x) ∂volume := by
      refine setIntegral_congr_fun
        (Homogenization.isOpenBoundedConvexDomain_openCubeSet Q).isOpen.measurableSet
        fun x _ ↦ ?_
      rw [hA x, scalarCoeffField, matVecMul_scalarMatrix]
    have hp := hpair phi
    rw [hmass] at hp
    show (∫ x in openCubeSet Q,
        vecDot (matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume) =
      ∫ x in openCubeSet Q,
        vecDot (F.toField x) (phi.toH1Function.grad x) ∂volume
    rw [hlhs]
    linarith [heq, hp]
  · have hvol : 0 < cubeVolume Q := cubeVolume_pos Q
    have hsqrt_pos : 0 < Real.sqrt (cubeVolume Q) := Real.sqrt_pos.mpr hvol
    have hnormEq : ‖toScalarL2 hmem‖ = |mu| * ‖toScalarL2 u.memL2‖ :=
      norm_toScalarL2_const_mul u.memL2 mu
    have huNorm : ‖toScalarL2 u.memL2‖ =
        Real.sqrt (cubeVolume Q) * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun := by
      have h := norm_toScalarL2_openCubeSet_eq_volume_rpow_half_mul_cubeLpNorm_two
        Q u.memL2_normalizedCubeMeasure
      rw [Real.sqrt_eq_rpow]
      exact h
    have hgrad : F.gradientCoordL2NormSum ≤
        Clift * (|mu| * (Real.sqrt (cubeVolume Q) *
          cubeLpNorm Q (2 : ℝ≥0∞) u.toFun)) := by
      rw [← huNorm, ← hnormEq]
      exact hnorm
    have hrel : F.relativeGradientCoordL2NormSum ≤
        (cubeScaleFactor Q / Real.sqrt (cubeVolume Q)) *
          (Clift * (|mu| * (Real.sqrt (cubeVolume Q) *
            cubeLpNorm Q (2 : ℝ≥0∞) u.toFun))) := by
      unfold CubeVectorH1Function.relativeGradientCoordL2NormSum
      refine mul_le_mul_of_nonneg_left hgrad ?_
      exact div_nonneg (le_of_lt (cubeScaleFactor_pos' Q)) (Real.sqrt_nonneg _)
    have hcancel :
        (cubeScaleFactor Q / Real.sqrt (cubeVolume Q)) *
            (Clift * (|mu| * (Real.sqrt (cubeVolume Q) *
              cubeLpNorm Q (2 : ℝ≥0∞) u.toFun))) =
          Clift * (cubeScaleFactor Q *
            (|mu| * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun)) := by
      field_simp
    calc
      Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s F.toField
          ≤ besovH1GradientConstant d s * F.relativeGradientCoordL2NormSum :=
            scaleNormalizedPositiveBesovVectorSeminormTwo_toField_le Q F hs
      _ ≤ besovH1GradientConstant d s *
            (Clift * (cubeScaleFactor Q *
              (|mu| * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun))) := by
            refine mul_le_mul_of_nonneg_left ?_ (besovH1GradientConstant_nonneg d s)
            rw [← hcancel]
            exact hrel
      _ = (besovH1GradientConstant d s * Clift) *
            (cubeScaleFactor Q * (|mu| * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun)) := by
            ring

/-! ## The mesoscopic Caccioppoli balance -/

/-- The `t`-dependent constant of the mesoscopic Caccioppoli balance: the
Caccioppoli forcing weight `t⁻⁸/(1-2t)` times the square of the datum constant
of `exists_mesoscopic_forced_datum`. -/
def mesoscopicBalanceConstant (t Clift : ℝ) : ℝ :=
  9 + (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) * Clift ^ 2

/-- **The mesoscopic Caccioppoli balance.**

Running the coarse Caccioppoli inequality with right-hand side
(`SubdiffusiveProcess.CoarseGrainingVocab.exists_interior_caccioppoli_raw`, an *arbitrary*
triadic cube and an arbitrary interior core) on the datum produced by
`exists_mesoscopic_forced_datum`, the two terms of its right-hand side read

```
T ⟨a|∇u|²⟩_core ≲ Θ · ( (λ T w⁻²) + C_t (w²/(λ T)) ) · ⟨u²⟩_Q ,
```

with `w = side(Q)`.  They *balance* at `w² ≍ λ_t(Q;a) T`, which is the
manuscript's "optimized in the mesoscopic scale"
with the following balance: at the top scale the second term is larger
by `(ℓ/(λT)^{1/2})² ≫ 1`, which is why the unit-scale lift is useless.
Under the two-sided balance hypothesis
`w² ≤ λ T ≤ 9 w²` both terms are `O(1)` and the coarse energy bound holds with
`Gam ≍ Θ_{s,t}(Q;a) ≍ Λ/λ`, exactly the size assumed by
`mesoscopic_smallness_of_paper_condition`. -/
theorem exists_mesoscopic_caccioppoli_balance_const (d : ℕ) [NeZero d] {t : ℝ}
    (ht : 0 < t) (ht2 : t < 1 / 2) :
    ∃ Ccacc C1 : ℝ, 0 < Ccacc ∧ 0 ≤ C1 ∧
      ∀ (Q : TriadicCube d) (afam : Ch03.CoeffFamily d) (a : Vec d → ℝ)
        (s T K : ℝ) (x : Vec d) (u : H1Function (openCubeSet Q)),
        (∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y) →
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) T⁻¹ (openCubeSet Q) u
          (fun _ ↦ (0 : ℝ)) →
        0 < s → s < 1 → s + t < 1 → 0 < T → 0 ≤ K →
        openCubeAtScale x (Q.scale - 1) ⊆ openCubeSet Q →
        (cubeScaleFactor Q) ^ 2 ≤ Ch02.lambdaS Q t afam * T →
        Ch02.lambdaS Q t afam * T ≤ K * (cubeScaleFactor Q) ^ 2 →
        T * localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (afam.coeffOn Q) u ≤
          caccioppoliWithRHSPrefactor Ccacc Q afam s t * (K + C1) *
            cubeLpNorm Q (2 : ℝ≥0∞) u.toFun ^ 2 := by
  classical
  obtain ⟨Ccacc, hCcacc, hcacc⟩ := exists_interior_caccioppoli_raw d
  obtain ⟨Clift, hClift0, hlift⟩ :=
    exists_mesoscopic_forced_datum d (s := 2 * t) (by linarith)
  refine ⟨Ccacc, Real.rpow t (-8 : ℝ) / (1 - 2 * t) * Clift ^ 2, hCcacc, ?_, ?_⟩
  · have : (0 : ℝ) ≤ Real.rpow t (-8 : ℝ) / (1 - 2 * t) :=
      div_nonneg (Real.rpow_nonneg ht.le _) (by linarith)
    positivity
  intro Q afam a s T K x u hA hu hs hs1 hst hT hK hpatch hbal_lo hbal_hi
  obtain ⟨g, hforced, hgreg, hgbound⟩ := hlift Q afam a hA T⁻¹ u hu
  have hraw := hcacc (Q := Q) (a := afam) (s := s) (t := t) (x := x) (g := g)
    u hforced hs hs1 ht ht2 hst hpatch hgreg
  -- notation
  set lam : ℝ := Ch02.lambdaS Q t afam with hlamdef
  have hlam_pos : 0 < lam := by
    have := Ch02.lambdaSq_pos (d := d) Q afam (s := t)
      (q := Ch02.MultiscaleExponent.finite 1) ht
      (by norm_num [Ch02.MultiscaleExponent.IsAdmissible])
    simpa [hlamdef, Ch02.lambdaS] using this
  set w : ℝ := cubeScaleFactor Q with hwdef
  have hw_pos : 0 < w := cubeScaleFactor_pos' Q
  set N : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) u.toFun with hNdef
  have hN0 : 0 ≤ N := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) u.toFun
  have hmassEq : normalizedL2SqOnSet (openCubeSet Q) u.toFun = N ^ 2 :=
    normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq Q u.toFun
      u.memL2_normalizedCubeMeasure
  have hscaleEq : Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) = (w ^ 2)⁻¹ := by
    have hcast : (-2 : ℝ) * (((Q.scale : ℤ) : ℝ)) = ((((-2) * Q.scale : ℤ)) : ℝ) := by
      push_cast; ring
    have hint : Real.rpow (3 : ℝ) (((((-2) * Q.scale : ℤ))) : ℝ) =
        (3 : ℝ) ^ ((-2) * Q.scale : ℤ) :=
      Real.rpow_intCast (3 : ℝ) (((-2) * Q.scale : ℤ))
    rw [hcast, hint, hwdef]
    simp only [cubeScaleFactor]
    rw [mul_comm ((-2 : ℤ)) Q.scale, zpow_mul,
      show ((-2 : ℤ)) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
  have hlamInv : Real.rpow lam (-1 : ℝ) = lam⁻¹ := Real.rpow_neg_one lam
  have hPref0 : 0 ≤ caccioppoliWithRHSPrefactor Ccacc Q afam s t :=
    caccioppoliWithRHSPrefactor_nonneg hCcacc.le hs ht hst
  -- the Besov datum square
  have hB0 : 0 ≤ Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hgreg
  have hmuAbs : |T⁻¹| = T⁻¹ := abs_of_pos (inv_pos.mpr hT)
  have hBsq : Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2 ≤
      Clift ^ 2 * (w ^ 2 * (T⁻¹ ^ 2 * N ^ 2)) := by
    have hle : Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ≤
        Clift * (w * (T⁻¹ * N)) := by
      simpa [hmuAbs, hwdef, hNdef] using hgbound
    have hrhs0 : 0 ≤ Clift * (w * (T⁻¹ * N)) := by
      have hT0 : 0 ≤ T⁻¹ := (inv_pos.mpr hT).le
      positivity
    calc
      Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2
          ≤ (Clift * (w * (T⁻¹ * N))) ^ 2 :=
            pow_le_pow_left₀ hB0 hle 2
      _ = Clift ^ 2 *
            (w ^ 2 * (T⁻¹ ^ 2 * N ^ 2)) := by ring
  -- assemble
  have hKt0 : 0 ≤ Real.rpow t (-8 : ℝ) / (1 - 2 * t) :=
    div_nonneg (Real.rpow_nonneg ht.le _) (by linarith)
  have hfirst : T * (lam * (w ^ 2)⁻¹ * N ^ 2) ≤ K * N ^ 2 := by
    have hw2 : (0 : ℝ) < w ^ 2 := by positivity
    have hr : lam * T * (w ^ 2)⁻¹ ≤ K := by
      rw [mul_inv_le_iff₀ hw2]
      linarith [hbal_hi]
    have heq : T * (lam * (w ^ 2)⁻¹ * N ^ 2) = (lam * T * (w ^ 2)⁻¹) * N ^ 2 := by
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hr (sq_nonneg N)
  have hsecond :
      T * ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) * lam⁻¹ *
          Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2) ≤
        (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
          Clift ^ 2 * N ^ 2 := by
    have hKl : 0 ≤ (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) * lam⁻¹ :=
      mul_nonneg hKt0 (inv_pos.mpr hlam_pos).le
    have hstep := mul_le_mul_of_nonneg_left hBsq hKl
    have hT0 : 0 < T := hT
    have hfin :
        T * ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) * lam⁻¹ *
          (Clift ^ 2 *
            (w ^ 2 * (T⁻¹ ^ 2 * N ^ 2)))) ≤
          (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
            Clift ^ 2 * N ^ 2 := by
      have hratio : w ^ 2 * (lam * T)⁻¹ ≤ 1 := by
        have hpos : 0 < lam * T := mul_pos hlam_pos hT
        rw [mul_inv_le_iff₀ hpos]
        simpa using hbal_lo
      have hTinv : T * (T⁻¹ ^ 2) = T⁻¹ := by
        field_simp
      have hCsq : 0 ≤ Clift ^ 2 := sq_nonneg _
      have hexp :
          T * ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) * lam⁻¹ *
            (Clift ^ 2 *
              (w ^ 2 * (T⁻¹ ^ 2 * N ^ 2)))) =
            (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
              Clift ^ 2 *
              ((w ^ 2 * (lam * T)⁻¹) * N ^ 2) := by
        field_simp
      rw [hexp]
      have hbase : 0 ≤ (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
          Clift ^ 2 := mul_nonneg hKt0 hCsq
      have : (w ^ 2 * (lam * T)⁻¹) * N ^ 2 ≤ 1 * N ^ 2 :=
        mul_le_mul_of_nonneg_right hratio (sq_nonneg N)
      calc
        (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
            Clift ^ 2 *
            ((w ^ 2 * (lam * T)⁻¹) * N ^ 2)
            ≤ (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
              Clift ^ 2 * (1 * N ^ 2) :=
              mul_le_mul_of_nonneg_left this hbase
        _ = (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
              Clift ^ 2 * N ^ 2 := by ring
    exact le_trans (by nlinarith [hstep, hT.le]) hfin
  have hcombined :
      T * localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (afam.coeffOn Q) u ≤
        caccioppoliWithRHSPrefactor Ccacc Q afam s t *
          (T * (lam * (w ^ 2)⁻¹ * N ^ 2) +
            T * ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) * lam⁻¹ *
              Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2)) := by
    have hraw' := mul_le_mul_of_nonneg_left hraw hT.le
    rw [hmassEq, hscaleEq, hlamInv] at hraw'
    calc
      T * localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (afam.coeffOn Q) u
          ≤ T * (caccioppoliWithRHSPrefactor Ccacc Q afam s t *
              (lam * (w ^ 2)⁻¹ * N ^ 2 +
                (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) * lam⁻¹ *
                  Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2)) := by
            simpa [hlamdef, hwdef, hNdef] using hraw'
      _ = caccioppoliWithRHSPrefactor Ccacc Q afam s t *
            (T * (lam * (w ^ 2)⁻¹ * N ^ 2) +
              T * ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) * lam⁻¹ *
                Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2)) := by
            ring
  refine hcombined.trans ?_
  have := add_le_add hfirst hsecond
  calc
    caccioppoliWithRHSPrefactor Ccacc Q afam s t *
        (T * (lam * (w ^ 2)⁻¹ * N ^ 2) +
          T * ((Real.rpow t (-8 : ℝ) / (1 - 2 * t)) * lam⁻¹ *
            Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2))
        ≤ caccioppoliWithRHSPrefactor Ccacc Q afam s t *
          (K * N ^ 2 +
            (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
              Clift ^ 2 * N ^ 2) :=
          mul_le_mul_of_nonneg_left this hPref0
    _ = caccioppoliWithRHSPrefactor Ccacc Q afam s t *
          (K + (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
            Clift ^ 2) * N ^ 2 := by ring

/-- **The mesoscopic Caccioppoli balance at the triadic constant `9`.**

The `K = 9` case of `exists_mesoscopic_caccioppoli_balance_const`, which is what
`exists_triadic_scale_balancing` delivers when the mesoscopic scale is chosen by
the Caccioppoli's own lower ellipticity.   -/
theorem exists_mesoscopic_caccioppoli_balance (d : ℕ) [NeZero d] {t : ℝ}
    (ht : 0 < t) (ht2 : t < 1 / 2) :
    ∃ Ccacc Gam : ℝ, 0 < Ccacc ∧ 0 ≤ Gam ∧
      ∀ (Q : TriadicCube d) (afam : Ch03.CoeffFamily d) (a : Vec d → ℝ)
        (s T : ℝ) (x : Vec d) (u : H1Function (openCubeSet Q)),
        (∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y) →
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) T⁻¹ (openCubeSet Q) u
          (fun _ ↦ (0 : ℝ)) →
        0 < s → s < 1 → s + t < 1 → 0 < T →
        openCubeAtScale x (Q.scale - 1) ⊆ openCubeSet Q →
        (cubeScaleFactor Q) ^ 2 ≤ Ch02.lambdaS Q t afam * T →
        Ch02.lambdaS Q t afam * T ≤ 9 * (cubeScaleFactor Q) ^ 2 →
        T * localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (afam.coeffOn Q) u ≤
          caccioppoliWithRHSPrefactor Ccacc Q afam s t * Gam *
            cubeLpNorm Q (2 : ℝ≥0∞) u.toFun ^ 2 := by
  obtain ⟨Ccacc, C1, hCcacc, hC1, h⟩ :=
    exists_mesoscopic_caccioppoli_balance_const d ht ht2
  refine ⟨Ccacc, 9 + C1, hCcacc, by linarith, ?_⟩
  intro Q afam a s T x u hA hu hs hs1 hst hT hpatch hlo hhi
  exact h Q afam a s T 9 x u hA hu hs hs1 hst hT (by norm_num) hpatch hlo hhi

/-! ## From the normalized balance to `CoarseEnergyBoundOn` -/

/-- With a scalar coefficient the localized coefficient energy is the plain
volume average of `a |∇u|²`. -/
theorem localizedCoeffEnergyValue_scalar
    {Q : TriadicCube d} {afam : CoeffFamily d} {a : Vec d → ℝ} (V : Set (Vec d))
    (hV : MeasurableSet V) (u : H1Function (openCubeSet Q))
    (hA : ∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y) :
    localizedCoeffEnergyValue V (afam.coeffOn Q) u =
      (volume V).toReal⁻¹ * ∫ y in V, a y * vecNormSq (u.grad y) ∂volume := by
  unfold localizedCoeffEnergyValue normalizedSetAverage Homogenization.volumeAverage
  congr 1
  refine setIntegral_congr_fun hV fun y _ ↦ ?_
  rw [hA y, scalarCoeffField, Ch02.symmPart_scalarMatrix, matVecMul_scalarMatrix,
    vecDot_smul_right]
  rfl

/-- **The coarse energy bound in the shape `CoarseEnergyBoundOn` consumes.**

The normalized balance of `exists_mesoscopic_caccioppoli_balance` transfers to
plain volume integrals with no loss: energy and mass are both averages, and the
core is contained in the cube, so the volume ratio is `≤ 1`. -/
theorem coarseEnergyBoundOn_of_normalized
    {Q : TriadicCube d} {afam : CoeffFamily d} {a : Vec d → ℝ} {x : Vec d}
    {T Gam : ℝ} (u : H1Function (openCubeSet Q))
    (hA : ∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y)
    (hx : x ∈ openCubeSet Q) (hGam : 0 ≤ Gam)
    (h : T * localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (afam.coeffOn Q) u ≤
      Gam * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun ^ 2) :
    CoarseEnergyBoundOn a (openCubeSet Q) (caccioppoliCoreSet Q x) u.toFun u.grad
      T Gam := by
  classical
  set V : Set (Vec d) := caccioppoliCoreSet Q x with hVdef
  have hVsub : V ⊆ openCubeSet Q := Set.inter_subset_left
  have hVopen : IsOpen V :=
    (isOpen_openCubeSet Q).inter (isOpen_openCubeAtScale x (Q.scale - 2))
  have hVmem : x ∈ V := ⟨hx, mem_openCubeAtScale_center x (Q.scale - 2)⟩
  have hVmeas : MeasurableSet V := measurableSet_caccioppoliCoreSet Q x
  have hVne : (volume V) ≠ 0 := (hVopen.measure_pos volume ⟨x, hVmem⟩).ne'
  have hVtop : (volume V) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_openCubeSet_lt_top Q).ne (measure_mono hVsub)
  have hcpos : 0 < (volume V).toReal := ENNReal.toReal_pos hVne hVtop
  have hQpos : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hratio : (volume V).toReal ≤ (volume (openCubeSet Q)).toReal :=
    ENNReal.toReal_mono (volume_openCubeSet_lt_top Q).ne (measure_mono hVsub)
  have henergy := localizedCoeffEnergyValue_scalar (Q := Q) (afam := afam) (a := a)
    V hVmeas u hA
  have hmassEq : cubeLpNorm Q (2 : ℝ≥0∞) u.toFun ^ 2 =
      (volume (openCubeSet Q)).toReal⁻¹ *
        ∫ y in openCubeSet Q, u.toFun y ^ 2 ∂volume := by
    have h := normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq Q u.toFun
      u.memL2_normalizedCubeMeasure
    rw [← h]
    rfl
  have hMnn : (0 : ℝ) ≤ ∫ y in openCubeSet Q, u.toFun y ^ 2 ∂volume :=
    setIntegral_nonneg (isOpen_openCubeSet Q).measurableSet fun y _ ↦ sq_nonneg _
  rw [henergy, hmassEq] at h
  show T * ∫ y in V, a y * vecNormSq (u.grad y) ∂volume ≤
    Gam * ∫ y in openCubeSet Q, u.toFun y ^ 2 ∂volume
  have hmul := mul_le_mul_of_nonneg_left h hcpos.le
  have hlhs : (volume V).toReal *
      (T * ((volume V).toReal⁻¹ * ∫ y in V, a y * vecNormSq (u.grad y) ∂volume)) =
      T * ∫ y in V, a y * vecNormSq (u.grad y) ∂volume := by
    field_simp
  rw [hlhs] at hmul
  refine hmul.trans ?_
  have hfrac : (volume V).toReal * (volume (openCubeSet Q)).toReal⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hQpos]
    simpa using hratio
  calc
    (volume V).toReal *
        (Gam * ((volume (openCubeSet Q)).toReal⁻¹ *
          ∫ y in openCubeSet Q, u.toFun y ^ 2 ∂volume))
        = ((volume V).toReal * (volume (openCubeSet Q)).toReal⁻¹) *
            (Gam * ∫ y in openCubeSet Q, u.toFun y ^ 2 ∂volume) := by ring
    _ ≤ 1 * (Gam * ∫ y in openCubeSet Q, u.toFun y ^ 2 ∂volume) := by
          exact mul_le_mul_of_nonneg_right hfrac (mul_nonneg hGam hMnn)
    _ = Gam * ∫ y in openCubeSet Q, u.toFun y ^ 2 ∂volume := by ring

/-- **`CoarseEnergyBoundOn` for the homogeneous massive equation at the
mesoscopic scale.**

On a triadic cube whose side satisfies
`w² ≤ λ_t(Q;a) T ≤ 9 w²`, the coarse Caccioppoli inequality with the mesoscopic
Dirichlet `H²` datum gives the coarse energy bound with
`Gam = Θ_{s,t}(Q;a)`-sized constant, the energy taken on the Caccioppoli core
and the mass on the whole cube — the genuine Caccioppoli shape that the
three-set predicate of `WholeSpaceRowsMesoscopicSplit.lean` was designed for. -/
theorem exists_mesoscopic_coarseEnergyBoundOn (d : ℕ) [NeZero d] {t : ℝ}
    (ht : 0 < t) (ht2 : t < 1 / 2) :
    ∃ Ccacc Gam0 : ℝ, 0 < Ccacc ∧ 0 ≤ Gam0 ∧
      ∀ (Q : TriadicCube d) (afam : CoeffFamily d) (a : Vec d → ℝ)
        (s T : ℝ) (x : Vec d) (u : H1Function (openCubeSet Q)),
        (∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y) →
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) T⁻¹ (openCubeSet Q) u
          (fun _ ↦ (0 : ℝ)) →
        0 < s → s < 1 → s + t < 1 → 0 < T →
        openCubeAtScale x (Q.scale - 1) ⊆ openCubeSet Q →
        (cubeScaleFactor Q) ^ 2 ≤ Ch02.lambdaS Q t afam * T →
        Ch02.lambdaS Q t afam * T ≤ 9 * (cubeScaleFactor Q) ^ 2 →
        CoarseEnergyBoundOn a (openCubeSet Q) (caccioppoliCoreSet Q x) u.toFun
          u.grad T (caccioppoliWithRHSPrefactor Ccacc Q afam s t * Gam0) := by
  classical
  obtain ⟨Ccacc, Gam0, hCcacc, hGam0, hbal⟩ :=
    exists_mesoscopic_caccioppoli_balance d ht ht2
  refine ⟨Ccacc, Gam0, hCcacc, hGam0, ?_⟩
  intro Q afam a s T x u hA hu hs hs1 hst hT hpatch hlo hhi
  have hx : x ∈ openCubeSet Q := hpatch (mem_openCubeAtScale_center x (Q.scale - 1))
  have hPref0 : 0 ≤ caccioppoliWithRHSPrefactor Ccacc Q afam s t :=
    caccioppoliWithRHSPrefactor_nonneg hCcacc.le hs ht hst
  exact coarseEnergyBoundOn_of_normalized u hA hx (mul_nonneg hPref0 hGam0)
    (hbal Q afam a s T x u hA hu hs hs1 hst hT hpatch hlo hhi)

/-- **`CoarseEnergyBoundOn` with the mesoscopic scale fixed from outside.**

The `K`-generalization of `exists_mesoscopic_coarseEnergyBoundOn`: when the
mesoscopic scale is chosen by the *price*'s balance (in the deterministic
`lambda_{t/2,2}`) rather than by the Caccioppoli's own `lambda_{t,1}`, the two
lower ellipticities differ and the upper balance holds only with a constant
`K >= 9` (see `WholeSpaceRowsLayerBridge.lean` and `WholeSpaceRowsCellBalance.lean`);
`K` then enters the coarse energy constant additively. -/
theorem exists_mesoscopic_coarseEnergyBoundOn_const (d : ℕ) [NeZero d] {t : ℝ}
    (ht : 0 < t) (ht2 : t < 1 / 2) :
    ∃ Ccacc C1 : ℝ, 0 < Ccacc ∧ 0 ≤ C1 ∧
      ∀ (Q : TriadicCube d) (afam : CoeffFamily d) (a : Vec d → ℝ)
        (s T K : ℝ) (x : Vec d) (u : H1Function (openCubeSet Q)),
        (∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y) →
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) T⁻¹ (openCubeSet Q) u
          (fun _ ↦ (0 : ℝ)) →
        0 < s → s < 1 → s + t < 1 → 0 < T → 0 ≤ K →
        openCubeAtScale x (Q.scale - 1) ⊆ openCubeSet Q →
        (cubeScaleFactor Q) ^ 2 ≤ Ch02.lambdaS Q t afam * T →
        Ch02.lambdaS Q t afam * T ≤ K * (cubeScaleFactor Q) ^ 2 →
        CoarseEnergyBoundOn a (openCubeSet Q) (caccioppoliCoreSet Q x) u.toFun
          u.grad T (caccioppoliWithRHSPrefactor Ccacc Q afam s t * (K + C1)) := by
  classical
  obtain ⟨Ccacc, C1, hCcacc, hC1, hbal⟩ :=
    exists_mesoscopic_caccioppoli_balance_const d ht ht2
  refine ⟨Ccacc, C1, hCcacc, hC1, ?_⟩
  intro Q afam a s T K x u hA hu hs hs1 hst hT hK hpatch hlo hhi
  have hx : x ∈ openCubeSet Q := hpatch (mem_openCubeAtScale_center x (Q.scale - 1))
  have hPref0 : 0 ≤ caccioppoliWithRHSPrefactor Ccacc Q afam s t :=
    caccioppoliWithRHSPrefactor_nonneg hCcacc.le hs ht hst
  exact coarseEnergyBoundOn_of_normalized u hA hx
    (mul_nonneg hPref0 (by linarith))
    (hbal Q afam a s T K x u hA hu hs hs1 hst hT hK hpatch hlo hhi)

/-! ## The price with the datum carried inside the energy -/

/-- **The mesoscopic cross-term price with the `H²`-lift remainder carried
inside the energy.**

`MesoscopicCrossPriceOn`  puts the remainder of the Dirichlet `H²` lift
in a *separate* additive term `beta * S * t⁻¹ M`.  The route that actually
produces that remainder — bounding the negative Besov norm of the flux
`a∇u` by splitting it into a solenoidal part and the corrector flux of the
datum, whose coarse energy is `≲ λ⁻¹ [g]²_{B^{s,+}}` — produces it instead as an
*additive energy*: the flux's negative norm, which multiplies **both** branches
of the split price, is bounded by `cL √(Ea + Sc t⁻¹ M)`.  This predicate is that
shape.

It is not weaker: `massive_local_l2_coarse_contraction_of_energy_price_on` below
derives exactly the conclusion of
`massive_local_l2_coarse_contraction_of_price_on` from it, by absorbing the
datum energy into the coarse energy bound (`Gam ↦ Gam + Sc`).  The two shapes
are not comparable term by term — the `beta⁻¹` branch of this one is larger —
so both are kept. -/
def MesoscopicCrossPriceEnergyOn (a : Vec d → ℝ) (W V : Set (Vec d))
    (w : Vec d → ℝ) (G : Vec d → Vec d) (chi : Vec d → ℝ) (t P R Sc : ℝ) : Prop :=
  ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
    |2 * ∫ x in W, a x * chi x * w x *
        vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume| ≤
      beta * P * ((∫ x in V, a x * vecNormSq (G x) ∂volume) +
          Sc * (t⁻¹ * ∫ x in W, w x ^ 2 ∂volume)) +
        beta⁻¹ * R *
          Real.sqrt ((∫ x in V, a x * vecNormSq (G x) ∂volume) +
            Sc * (t⁻¹ * ∫ x in W, w x ^ 2 ∂volume)) *
          Real.sqrt (∫ x in W, w x ^ 2 ∂volume)

/-- **The coarse-grained local `L²` contraction from the energy-carried
price.**

Same conclusion as `massive_local_l2_coarse_contraction_of_price_on`, from the
energy-carried price and the *same* coarse energy bound; the datum energy `Sc`
is absorbed into `Gam`, so the smallness condition reads with `Gam + Sc` in
place of `Gam` and no separate `S`. -/
theorem massive_local_l2_coarse_contraction_of_energy_price_on
    {a : Vec d → ℝ} {lam Lam t eta P R Sc Gam K : ℝ} {W V S : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (ht : 0 < t) (heta : 0 < eta)
    (hP : 0 < P) (hGam : 0 < Gam) (hR : 0 ≤ R) (hSc : 0 ≤ Sc)
    (hbeta1 : eta ≤ 3 * (P * (Gam + Sc)))
    (hSW : S ⊆ W) (hSmeas : MeasurableSet S)
    (u : H1Function W)
    (hu : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹ W u (fun _ ↦ (0 : ℝ)))
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi) (hchiS : tsupport chi ⊆ W)
    (hchi_le : ∀ x, |chi x| ≤ 1) (hchi_one : ∀ x ∈ S, chi x = 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K)
    (hprice : MesoscopicCrossPriceEnergyOn a W V u.toFun u.grad chi t P R Sc)
    (henergy : CoarseEnergyBoundOn a W V u.toFun u.grad t Gam)
    (hsmall : 81 * (P * (Gam + Sc)) ^ 2 * R ^ 2 * (Gam + Sc) * t ≤ eta ^ 4) :
    (∫ x in S, u.toFun x ^ 2 ∂volume) +
        t * ∫ x in S, a x * vecNormSq (u.grad x) ∂volume ≤
      eta * ∫ x in W, u.toFun x ^ 2 ∂volume := by
  classical
  have hWmeas : MeasurableSet W := hW.isOpen.measurableSet
  have hMnn : (0 : ℝ) ≤ ∫ x in W, u.toFun x ^ 2 ∂volume :=
    setIntegral_nonneg hWmeas fun x _ ↦ sq_nonneg _
  set M : ℝ := ∫ x in W, u.toFun x ^ 2 ∂volume with hMdef
  set Ea : ℝ := ∫ x in V, a x * vecNormSq (u.grad x) ∂volume with hEadef
  set E' : ℝ := Ea + Sc * (t⁻¹ * M) with hE'def
  have hstep : ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
      t⁻¹ * (∫ x in S, u.toFun x ^ 2 ∂volume) +
          ∫ x in S, a x * vecNormSq (u.grad x) ∂volume ≤
        beta * P * E' + beta⁻¹ * R * Real.sqrt E' * Real.sqrt M +
          beta * 0 * (t⁻¹ * M) + 0 := by
    intro beta hbeta hbeta1'
    have hforce : |∫ x in W, (fun _ ↦ (0 : ℝ)) x * chi x ^ 2 * u.toFun x ∂volume| ≤ 0 := by
      simp
    have := massive_cutoff_mass_energy_le_of_cross_bound hW hEll haNonneg ht hSW hSmeas
      u hu hchi hchiC hchiS hchi_le hchi_one hK (hprice beta hbeta hbeta1') hforce
    simpa [hE'def, hEadef, hMdef] using by linarith [this]
  have henergy' : t * E' ≤ (Gam + Sc) * M := by
    have h1 : t * Ea ≤ Gam * M := henergy
    have h2 : t * (Sc * (t⁻¹ * M)) = Sc * M := by
      field_simp
    calc
      t * E' = t * Ea + t * (Sc * (t⁻¹ * M)) := by rw [hE'def]; ring
      _ = t * Ea + Sc * M := by rw [h2]
      _ ≤ Gam * M + Sc * M := by linarith
      _ = (Gam + Sc) * M := by ring
  have hmain := mesoscopic_mass_contraction (t := t) (eta := eta) (P := P) (R := R)
    (S := 0) (Gam := Gam + Sc) (m := ∫ x in S, u.toFun x ^ 2 ∂volume)
    (e := ∫ x in S, a x * vecNormSq (u.grad x) ∂volume)
    (E := E') (M := M) (D := 0)
    ht heta hP (by linarith) hR le_rfl hMnn (by simpa using hbeta1) hstep henergy'
    (by simpa using hsmall)
  linarith [hmain]

/-! ## The mesoscopic scale exists -/

/-- **The balance hypothesis is realizable.**  For every positive `y` (in the
application `y = λ_t(Q;a) T`) there is a triadic scale `m` with
`(3^m)² ≤ y ≤ 9 (3^m)²`, so the two-sided balance hypothesis of
`exists_mesoscopic_caccioppoli_balance` is satisfied by some triadic cube side,
and the mesoscopic depth is `m = ⌊log₉ y⌋`.  The loss `9` is the triadic
granularity of the scale: no smaller factor is available. -/
theorem exists_triadic_scale_balancing {y : ℝ} (hy : 0 < y) :
    ∃ m : ℤ, ((3 : ℝ) ^ m) ^ 2 ≤ y ∧ y ≤ 9 * ((3 : ℝ) ^ m) ^ 2 := by
  classical
  refine ⟨Int.log 9 y, ?_, ?_⟩
  · have hsq : ((3 : ℝ) ^ (Int.log 9 y)) ^ 2 = ((9 : ℝ)) ^ (Int.log 9 y) := by
      rw [sq, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
        show (9 : ℝ) = (3 : ℝ) ^ (2 : ℕ) by norm_num,
        ← zpow_natCast (3 : ℝ) 2, ← zpow_mul]
      ring_nf
    rw [hsq]
    have := Int.zpow_log_le_self (R := ℝ) (b := 9) (r := y) (by norm_num) hy
    simpa using this
  · have hsq : ((3 : ℝ) ^ (Int.log 9 y)) ^ 2 = ((9 : ℝ)) ^ (Int.log 9 y) := by
      rw [sq, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
        show (9 : ℝ) = (3 : ℝ) ^ (2 : ℕ) by norm_num,
        ← zpow_natCast (3 : ℝ) 2, ← zpow_mul]
      ring_nf
    rw [hsq]
    have hlt := Int.lt_zpow_succ_log_self (R := ℝ) (b := 9) (by norm_num) y
    have hsucc : ((9 : ℝ)) ^ (Int.log 9 y + 1) = 9 * ((9 : ℝ)) ^ (Int.log 9 y) := by
      rw [zpow_add₀ (by norm_num : (9 : ℝ) ≠ 0)]
      simp [mul_comm]
    have : y < 9 * ((9 : ℝ)) ^ (Int.log 9 y) := by
      simpa [hsucc] using hlt
    exact this.le

/-! ## The smallness condition against the library's actual prefactor -/

/-- **The manuscript's smallness condition, with the coarse energy constant a
`Theta`-shaped quantity.**

`mesoscopic_smallness_of_paper_condition`  assumes `Gam ≤ c (Λ/λ)`.  The
coarse energy bound this file proves has
`Gam = caccioppoliWithRHSPrefactor C Q a s t * Gam0`, whose ellipticity content
is `Θ_{s,t}(Q;a)^{(1-t)/(1-s-t)}` — a *power* `> 1` of the ratio, not the ratio
itself.  This version replaces `Λ/λ` by an abstract `Theta ≥ 1` and isolates the
one place the ratio structure is used, the domination hypothesis
`Theta⁴ Λ ≤ Λ¹² λ⁻¹¹`.  version is the case `Theta = Λ/λ`. -/
theorem mesoscopic_smallness_of_paper_condition_theta
    {t lam Lam eta c P R Ssmall Gam Theta : ℝ} (ht : 0 < t) (hlam : 0 < lam)
    (hlamLam : lam ≤ Lam) (hc : 0 < c) (hGam0 : 0 ≤ Gam) (hTheta : 1 ≤ Theta)
    (hPS : (P * Gam + Ssmall) ^ 2 ≤ c * Theta ^ 3)
    (hR : R ^ 2 ≤ c * Lam) (hGam : Gam ≤ c * Theta)
    (hdom : Theta ^ 4 * Lam ≤ Lam ^ 12 * lam⁻¹ ^ 11)
    (hcond : t * (Lam ^ 12 * lam⁻¹ ^ 11) ≤ (81 * c ^ 3)⁻¹ * eta ^ 4) :
    81 * (P * Gam + Ssmall) ^ 2 * R ^ 2 * Gam * t ≤ eta ^ 4 := by
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hlamLam
  have hTheta0 : 0 < Theta := lt_of_lt_of_le zero_lt_one hTheta
  have h1 : (P * Gam + Ssmall) ^ 2 * R ^ 2 ≤ (c * Theta ^ 3) * (c * Lam) :=
    mul_le_mul hPS hR (sq_nonneg R) (by positivity)
  have h2 : (P * Gam + Ssmall) ^ 2 * R ^ 2 * Gam ≤
      (c * Theta ^ 3) * (c * Lam) * (c * Theta) :=
    mul_le_mul h1 hGam hGam0 (by positivity)
  have hcollect : (c * Theta ^ 3) * (c * Lam) * (c * Theta) =
      c ^ 3 * (Theta ^ 4 * Lam) := by ring
  have hstep : (P * Gam + Ssmall) ^ 2 * R ^ 2 * Gam ≤
      c ^ 3 * (Lam ^ 12 * lam⁻¹ ^ 11) := by
    refine h2.trans ?_
    rw [hcollect]
    exact mul_le_mul_of_nonneg_left hdom (by positivity)
  have hc3 : (0 : ℝ) < c ^ 3 := by positivity
  have hfinal : 81 * ((P * Gam + Ssmall) ^ 2 * R ^ 2 * Gam) * t ≤
      81 * (c ^ 3 * (Lam ^ 12 * lam⁻¹ ^ 11)) * t := by
    have := mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 81)
    exact mul_le_mul_of_nonneg_right this ht.le
  have harith : 81 * (c ^ 3 * (Lam ^ 12 * lam⁻¹ ^ 11)) * t ≤ eta ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_left hcond (by positivity : (0 : ℝ) ≤ 81 * c ^ 3)
    have hsimp : (81 * c ^ 3) * ((81 * c ^ 3)⁻¹ * eta ^ 4) = eta ^ 4 := by
      field_simp
    calc
      81 * (c ^ 3 * (Lam ^ 12 * lam⁻¹ ^ 11)) * t
          = (81 * c ^ 3) * (t * (Lam ^ 12 * lam⁻¹ ^ 11)) := by ring
      _ ≤ (81 * c ^ 3) * ((81 * c ^ 3)⁻¹ * eta ^ 4) := hmul
      _ = eta ^ 4 := hsimp
  calc
    81 * (P * Gam + Ssmall) ^ 2 * R ^ 2 * Gam * t
        = 81 * ((P * Gam + Ssmall) ^ 2 * R ^ 2 * Gam) * t := by ring
    _ ≤ 81 * (c ^ 3 * (Lam ^ 12 * lam⁻¹ ^ 11)) * t := hfinal
    _ ≤ eta ^ 4 := harith

/-- The domination hypothesis of `mesoscopic_smallness_of_paper_condition_theta`
holds whenever `Theta ≤ (Λ/λ)²`.  Since the library's prefactor carries
`Θ_{s,t}^{(1-t)/(1-s-t)}` and `(1-t)/(1-s-t) ≤ 2` as soon as `2s + t ≤ 1` (true
at the manuscript's indices), the manuscript's condition
`t Λ¹² λ⁻¹¹ ≤ C⁻¹ η^{15/2}` does cover the coarse energy constant that the
Caccioppoli route actually produces — the exponent budget `Λ¹²λ⁻¹¹` is not
exhausted by the extra power. -/
theorem theta_pow_two_dominates {lam Lam Theta : ℝ} (hlam : 0 < lam)
    (hlamLam : lam ≤ Lam) (hTheta1 : 1 ≤ Theta)
    (hTheta : Theta ≤ (Lam / lam) ^ 2) :
    Theta ^ 4 * Lam ≤ Lam ^ 12 * lam⁻¹ ^ 11 := by
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hlamLam
  have hratio : (1 : ℝ) ≤ Lam / lam := (one_le_div hlam).2 hlamLam
  have hTheta0 : 0 < Theta := lt_of_lt_of_le zero_lt_one hTheta1
  have h4 : Theta ^ 4 ≤ ((Lam / lam) ^ 2) ^ 4 :=
    pow_le_pow_left₀ hTheta0.le hTheta 4
  have hA : ((Lam / lam) ^ 2) ^ 4 * Lam = Lam ^ 9 * lam⁻¹ ^ 8 := by
    field_simp
  have hB : Lam ^ 12 * lam⁻¹ ^ 11 = (Lam ^ 9 * lam⁻¹ ^ 8) * (Lam / lam) ^ 3 := by
    field_simp
  have hC : (1 : ℝ) ≤ (Lam / lam) ^ 3 := one_le_pow₀ hratio
  have hD : (0 : ℝ) ≤ Lam ^ 9 * lam⁻¹ ^ 8 := by positivity
  calc
    Theta ^ 4 * Lam ≤ ((Lam / lam) ^ 2) ^ 4 * Lam :=
      mul_le_mul_of_nonneg_right h4 hLam.le
    _ = Lam ^ 9 * lam⁻¹ ^ 8 := hA
    _ ≤ (Lam ^ 9 * lam⁻¹ ^ 8) * (Lam / lam) ^ 3 := by nlinarith [hC, hD]
    _ = Lam ^ 12 * lam⁻¹ ^ 11 := hB.symm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
