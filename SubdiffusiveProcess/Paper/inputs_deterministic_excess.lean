module

public import SubdiffusiveProcess.Paper.inputs_det_excess_large_gap
public import SubdiffusiveProcess.Paper.inputs_deterministic_boundary
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.PaperErrorBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEllipticityCaps
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.StabilityIndexCube
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Observables
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.CutoffPaperError
public import SubdiffusiveProcess.Section6.CutoffRegularityGoodScales
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.AnchorInterior
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.FractionalHolderBridge

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open scoped BigOperators ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.Paper

/-- The finite-gap coefficient in excess quasi-monotonicity is dominated by
the first decay factor when the scale gap is below six. -/
theorem aux_inputs_deterministic_excess_small_gap_coefficient
    (d : ℕ) {k : ℕ} (hk : k < 6) :
    (3 : ℝ) ^ (k : ℤ) *
        Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d) ≤
      (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) *
        (3 : ℝ) ^ (-(k : ℝ) / 2) := by
  have hC0 : (0 : ℝ) ≤ 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) :=
    mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hA1 : (3 : ℝ) ^ (k : ℤ) ≤ 243 := by
    calc
      (3 : ℝ) ^ (k : ℤ) ≤ (3 : ℝ) ^ (5 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 243 := by norm_num
  have hA2 : Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d) ≤
      Real.sqrt ((3 : ℝ) ^ (7 * d)) := by
    refine Real.sqrt_le_sqrt ?_
    calc
      ((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d ≤ ((3 : ℝ) ^ (7 : ℤ)) ^ d :=
        pow_le_pow_left₀ (zpow_nonneg (by norm_num) _)
          (zpow_le_zpow_right₀ (by norm_num) (by omega)) d
      _ = (3 : ℝ) ^ (7 * d) := by
        rw [show (7 : ℤ) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast, ← pow_mul]
  have hA3 : (3 : ℝ) ^ (-(3 : ℝ)) ≤ (3 : ℝ) ^ (-(k : ℝ) / 2) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hkr : (k : ℝ) ≤ 5 := by exact_mod_cast (by omega : k ≤ 5)
    linarith
  have hA4 : (3 : ℝ) ^ (-(3 : ℝ)) = 1 / 27 := by
    rw [show (-(3 : ℝ)) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have hsq0 : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ (7 * d)) := Real.sqrt_nonneg _
  have hsq1 : (0 : ℝ) ≤ Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d) :=
    Real.sqrt_nonneg _
  have hzp : (0 : ℝ) < (3 : ℝ) ^ (k : ℤ) := zpow_pos (by norm_num) _
  have hleft : (3 : ℝ) ^ (k : ℤ) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d)
      ≤ 243 * Real.sqrt ((3 : ℝ) ^ (7 * d)) :=
    mul_le_mul hA1 hA2 hsq1 (by norm_num)
  have hmid : (243 : ℝ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) =
      (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) * ((1 : ℝ) / 27) := by
    rw [show ((3 : ℝ) ^ (8 : ℕ)) = 6561 by norm_num]
    ring
  have hright :
      (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) * ((1 : ℝ) / 27) ≤
        (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) *
          (3 : ℝ) ^ (-(k : ℝ) / 2) := by
    rw [← hA4]
    exact mul_le_mul_of_nonneg_left hA3 hC0
  linarith

/-- Excess quasi-monotonicity closes every gap below six using only the
scale-`n` excess. -/
theorem aux_inputs_deterministic_excess_small_gap
    (d : ℕ) [NeZero d] {m n k : ℕ} {x : Vec d}
    (hx : x ∈ cube d m) (hnm : n + 5 ≤ m) (_hkn : k ≤ n) (hk : k < 6)
    (u : H1Function (openCubeSet (originCube d m))) :
    excess (n - k) (truncatedCube d m (n - k) x) u.toFun ≤
      (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) *
        (3 : ℝ) ^ (-(k : ℝ) / 2) *
        excess n (truncatedCube d m n x) u.toFun := by
  have hu_n : MemLp u.toFun 2 (volume.restrict (truncatedCube d m n x)) :=
    u.memL2.mono_measure
      (Measure.restrict_mono
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.truncatedCube_subset_cube d m n x)
        le_rfl)
  have hcrude := SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.excess_truncatedCube_le
    (m := (m : ℤ)) (j := (n : ℤ) - (k : ℤ)) (l := (n : ℤ)) (x := x)
    hx (by omega) (by omega) (by omega) hu_n
  rw [show (n : ℤ) - ((n : ℤ) - (k : ℤ)) = (k : ℤ) by ring] at hcrude
  have hcoef := aux_inputs_deterministic_excess_small_gap_coefficient d hk
  have hE : 0 ≤ excess (n : ℤ) (truncatedCube d m n x) u.toFun :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.excess_nonneg _ _ _
  calc
    excess ((n : ℤ) - (k : ℤ)) (truncatedCube d m (n - k) x) u.toFun
        ≤ (3 : ℝ) ^ (k : ℤ) *
            Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d) *
              excess (n : ℤ) (truncatedCube d m n x) u.toFun := hcrude
    _ ≤ (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) *
          (3 : ℝ) ^ (-(k : ℝ) / 2) *
            excess (n : ℤ) (truncatedCube d m n x) u.toFun :=
      mul_le_mul_of_nonneg_right hcoef hE

/-- A finite paper-error cap transfers to the same real cap after `toReal`. -/
theorem aux_inputs_deterministic_excess_toReal_cap
    {err : ENNReal} {B : ℝ} (hB : 0 ≤ B) (herr : err ≤ ENNReal.ofReal B) :
    err.toReal ≤ B := by
  calc
    err.toReal ≤ (ENNReal.ofReal B).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top herr
    _ = B := ENNReal.toReal_ofReal hB

/-- Numerical closure for a small-gap estimate: a larger first-term
coefficient and nonnegative source prices absorb it into the full bound. -/
theorem aux_inputs_deterministic_excess_small_gap_rhs
    {K C D q E L R₂ R₃ R₄ : ℝ}
    (hKC : K ≤ C) (hC : 0 ≤ C) (hD : 0 ≤ D) (hq : 0 ≤ q)
    (hE : 0 ≤ E) (hR₂ : 0 ≤ R₂) (hR₃ : 0 ≤ R₃) (hR₄ : 0 ≤ R₄)
    (hsmall : L ≤ K * D * E) :
    L ≤ C * (D + q) * E + R₂ + R₃ + R₄ := by
  calc
    L ≤ K * D * E := hsmall
    _ ≤ C * D * E := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKC hD) hE
    _ ≤ C * (D + q) * E := by
      calc
        C * D * E = C * (D * E) := by ring
        _ ≤ C * ((D + q) * E) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hq) hE) hC
        _ = C * (D + q) * E := by ring
    _ ≤ C * (D + q) * E + R₂ + R₃ + R₄ := by
      calc
        C * (D + q) * E ≤ C * (D + q) * E + (R₂ + (R₃ + R₄)) :=
          le_add_of_nonneg_right (add_nonneg hR₂ (add_nonneg hR₃ hR₄))
        _ = C * (D + q) * E + R₂ + R₃ + R₄ := by ring

/-- The Chapter 2 full-block error for any scalar certificate is dominated by
the paper's scalar-probe error at the same root cube. -/
theorem aux_inputs_deterministic_excess_localError_le_paper
    (d : ℕ) [NeZero d] {b : Vec d → ℝ} (data : ScalarTriadicCoeffData b)
    {Q : Homogenization.TriadicCube d} {t a0 : ℝ}
    (ht : 0 < t) (ha0 : 0 < a0) :
    ENNReal.ofReal
        (Homogenization.Book.Ch02.HomogenizationErrorOnCube Q t
          .infinity (.finite 2) data.toTriadicCoeffFamily
          (Homogenization.scalarMatrix (d := d) a0)) ≤
      paperHomogenizationError Q Q.scale t .infinity (.finite 2)
        data.toTriadicCoeffFamily a0 := by
  exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ofReal_homogenizationErrorOnCube_infinity_two_le_paper
    Q data.toTriadicCoeffFamily (fun R => (data.onCube R).isSymmetric) ht ha0

/-- The paper's scalar error hypothesis supplies the chapter-level error cap
used by the local forced-replacement estimate. -/
theorem aux_inputs_deterministic_excess_chapter2Error_cap
    (d : ℕ) [NeZero d] {a : Vec d → ℝ} (data : ScalarTriadicCoeffData a)
    (Q : Homogenization.TriadicCube d) {t alpha B : ℝ}
    (ht : 0 < t) (halpha : 0 < alpha) (hB : 0 ≤ B)
    (hpaper : paperHomogenizationError Q Q.scale t .infinity (.finite 2)
      data.toTriadicCoeffFamily alpha ≤
      ENNReal.ofReal B) :
    Homogenization.Book.Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2)
        data.toTriadicCoeffFamily
        (Homogenization.scalarMatrix (d := d) alpha) ≤ B := by
  have hbridge :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ofReal_homogenizationErrorOnCube_infinity_two_le_paper
      Q data.toTriadicCoeffFamily (fun R => (data.onCube R).isSymmetric) ht halpha
  have hreal : ENNReal.ofReal
      (Homogenization.Book.Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2)
        data.toTriadicCoeffFamily
        (Homogenization.scalarMatrix (d := d) alpha)) ≤ ENNReal.ofReal B :=
    hbridge.trans hpaper
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hreal

/-- The larger `s/6` index has no larger error than the `s/8` cap appearing
in the target. -/
theorem aux_inputs_deterministic_excess_chapter2Error_cap_six
    (d : ℕ) [NeZero d] {a : Vec d → ℝ} (data : ScalarTriadicCoeffData a)
    (Q : Homogenization.TriadicCube d) {s alpha B : ℝ}
    (hs : 0 < s) (halpha : 0 < alpha) (hB : 0 ≤ B)
    (hpaper : paperHomogenizationError Q Q.scale (s / 8) .infinity (.finite 2)
      data.toTriadicCoeffFamily alpha ≤ ENNReal.ofReal B) :
    Homogenization.Book.Ch02.HomogenizationErrorOnCube Q (s / 6)
      .infinity (.finite 2) data.toTriadicCoeffFamily
      (Homogenization.scalarMatrix (d := d) alpha) ≤ B := by
  have hcap := aux_inputs_deterministic_excess_chapter2Error_cap
    d data Q (t := s / 8) (alpha := alpha) (B := B) (by positivity) halpha hB hpaper
  have hmono :=
    SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.homogenizationErrorOnCube_infinity_two_le_of_lt
      Q data.toTriadicCoeffFamily (Homogenization.scalarMatrix (d := d) alpha)
      (t := s / 8) (s := s / 6) (by positivity) (by linarith)
  exact hmono.trans hcap

/-- The local error on a root cube is unchanged when the supplied a.e.
coefficient family is replaced by its canonical pointwise representative. -/
theorem aux_inputs_deterministic_excess_rootPointwiseError_eq
    (d : ℕ) [NeZero d] (Q : Homogenization.TriadicCube d)
    {b : Vec d → ℝ} (data : ScalarTriadicCoeffData b)
    (t : ℝ) (a0 : Homogenization.Mat d) :
    Homogenization.Book.Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2)
        (data.toTriadicCoeffFamily) a0 =
      Homogenization.Book.Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2)
        (Homogenization.Book.Ch03.ABK26.rootPointwiseCoeffFamily Q
          ((data.toTriadicCoeffFamily).coeffOn Q)) a0 := by
  symm
  apply SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.homogenizationErrorOnCube_eq_of_descendantAEEq
    Q
  intro k S hS
  have hk : k ≤ Q.scale := Homogenization.scale_le_of_mem_descendantsAtScale hS
  exact SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.rootPointwiseCoeffFamily_descendant_aeeq_family
    Q data.toTriadicCoeffFamily hk hS

/-- The canonical root family is an exact, pointwise elliptic representative
on the anchor cube, as required by the off-grid stability interface. -/
theorem aux_inputs_deterministic_excess_rootPointwiseExact
    (d : ℕ) [NeZero d] {b : Vec d → ℝ}
    (data : ScalarTriadicCoeffData b) (Q : Homogenization.TriadicCube d) :
    let A := Homogenization.Book.Ch03.ABK26.rootPointwiseCoeffFamily Q
      (data.toTriadicCoeffFamily.coeffOn Q)
    (∀ R : Homogenization.TriadicCube d,
      (A.coeffOn R).toCoeffField =
        Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
          (Homogenization.Book.Ch02.cubeDomain Q)
          (data.toTriadicCoeffFamily.coeffOn Q)) ∧
      Homogenization.IsEllipticFieldOn
        (data.toTriadicCoeffFamily.coeffOn Q).lam
        (data.toTriadicCoeffFamily.coeffOn Q).Lam
        (Homogenization.cubeSet Q)
        (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
          (Homogenization.Book.Ch02.cubeDomain Q)
          (data.toTriadicCoeffFamily.coeffOn Q)) := by
  dsimp
  constructor
  · intro R
    rfl
  · exact Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn_cubeSet
      Q (data.toTriadicCoeffFamily.coeffOn Q)

/-- Exact-representative stability converts the anchored Chapter 2 error
cap into the off-grid error cap used in the local comparison argument. -/
theorem aux_inputs_deterministic_excess_offGridError_cap
    (d : ℕ) [NeZero d] {b : Vec d → ℝ}
    (data : ScalarTriadicCoeffData b)
    (Q P : Homogenization.TriadicCube d) (w : Vec d)
    {alpha t s B : ℝ} (hs : 0 < s) (hst : s < t) (ht : t ≤ 1 / 2)
    (hEll : Homogenization.IsEllipticFieldOn
      (data.toTriadicCoeffFamily.coeffOn Q).lam
      (data.toTriadicCoeffFamily.coeffOn Q).Lam
      (Homogenization.translateSet w
        (Homogenization.cubeSet P))
      (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
        (Homogenization.Book.Ch02.cubeDomain Q)
        (data.toTriadicCoeffFamily.coeffOn Q)))
    (hcontain : Homogenization.translateSet w
      (Homogenization.cubeSet P) ⊆ Homogenization.cubeSet Q)
    (herror : Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s
      .infinity (.finite 2) data.toTriadicCoeffFamily
      (Homogenization.scalarMatrix (d := d) alpha) ≤ B) :
    SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.offGridErrorFunctional w P t
      (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
        (Homogenization.Book.Ch02.cubeDomain Q)
        (data.toTriadicCoeffFamily.coeffOn Q))
      (Homogenization.scalarMatrix (d := d) alpha) ≤
      Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.offGridStabilityConst
        d t s) *
        ((3 : ℝ) ^ (s * (((Q.scale - P.scale).toNat : ℕ) : ℝ)) * B) := by
  let A := Homogenization.Book.Ch03.ABK26.rootPointwiseCoeffFamily Q
    (data.toTriadicCoeffFamily.coeffOn Q)
  let g := Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
    (Homogenization.Book.Ch02.cubeDomain Q)
    (data.toTriadicCoeffFamily.coeffOn Q)
  have hAExact := aux_inputs_deterministic_excess_rootPointwiseExact d data Q
  have herrorA : Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s
      .infinity (.finite 2) A (Homogenization.scalarMatrix (d := d) alpha) ≤ B := by
    calc
      Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s
          .infinity (.finite 2) A (Homogenization.scalarMatrix (d := d) alpha) =
          Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s
            .infinity (.finite 2) data.toTriadicCoeffFamily
            (Homogenization.scalarMatrix (d := d) alpha) := by
        symm
        exact aux_inputs_deterministic_excess_rootPointwiseError_eq d Q data s
          (Homogenization.scalarMatrix (d := d) alpha)
      _ ≤ B := herror
  have hstab := SubdiffusiveProcess.CoarseGrainingVocab.mathcalE_stability_infinity_two_of_exact_representative
    A (Homogenization.scalarMatrix (d := d) alpha) hs hst ht
    (by simpa [A, g] using hAExact.1) hEll hcontain
  calc
    SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.offGridErrorFunctional w P t g
        (Homogenization.scalarMatrix (d := d) alpha) ≤
      Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.offGridStabilityConst
        d t s) *
        ((3 : ℝ) ^ (s * (((Q.scale - P.scale).toNat : ℕ) : ℝ)) *
          Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s
            .infinity (.finite 2) A (Homogenization.scalarMatrix (d := d) alpha)) := hstab
    _ ≤ Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.offGridStabilityConst
        d t s) * ((3 : ℝ) ^ (s * (((Q.scale - P.scale).toNat : ℕ) : ℝ)) * B) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_left herrorA
        (Real.rpow_nonneg (by norm_num) _)

/-- Root pointwise ellipticity restricts to each measurable window contained in
the anchor cube. -/
theorem aux_inputs_deterministic_excess_rootPointwiseEllipticOn
    (d : ℕ) [NeZero d] {b : Vec d → ℝ}
    (data : ScalarTriadicCoeffData b) (Q : Homogenization.TriadicCube d)
    (U : Set (Vec d)) (hU : MeasurableSet U)
    (hUQ : U ⊆ Homogenization.cubeSet Q) :
    Homogenization.IsEllipticFieldOn
      (data.toTriadicCoeffFamily.coeffOn Q).lam
      (data.toTriadicCoeffFamily.coeffOn Q).Lam U
      (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
        (Homogenization.Book.Ch02.cubeDomain Q)
        (data.toTriadicCoeffFamily.coeffOn Q)) := by
  have hroot := aux_inputs_deterministic_excess_rootPointwiseExact d data Q
  exact hroot.2.mono hU hUQ

/-- The error hypothesis supplies the dimension-level coarse ellipticity caps
on the anchored root cube. -/
theorem aux_inputs_deterministic_excess_rootEllipticityCaps
    (d : ℕ) [NeZero d] {a : Vec d → ℝ} (data : ScalarTriadicCoeffData a)
    (Q : Homogenization.TriadicCube d) {s alpha Cerr epsilon : ℝ}
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (halpha : 0 < alpha)
    (hCerr : 0 < Cerr) (hepsilon : epsilon ∈ Set.Ioc (0 : ℝ) 1)
    (hpaper : paperHomogenizationError Q Q.scale (s / 8) .infinity (.finite 2)
      data.toTriadicCoeffFamily alpha ≤ ENNReal.ofReal (Cerr * epsilon)) :
    let B := 2 * (d : ℝ) * (Cerr ^ 2 + 1)
    alpha⁻¹ * Homogenization.Book.Ch02.LambdaSq Q (s / 6) (.finite 2)
        data.toTriadicCoeffFamily ≤ B ∧
      alpha * (Homogenization.Book.Ch02.lambdaSq Q (s / 6) (.finite 2)
        data.toTriadicCoeffFamily)⁻¹ ≤ B ∧
      Homogenization.Book.Ch02.LambdaS Q (1 / 2) data.toTriadicCoeffFamily ≤ B * alpha ∧
      (Homogenization.Book.Ch02.lambdaS Q (s / 3) data.toTriadicCoeffFamily)⁻¹ ≤ B * alpha⁻¹ ∧
      Homogenization.Book.Ch02.lambdaS Q (s / 3) data.toTriadicCoeffFamily ≤ B * alpha ∧
      Homogenization.Book.Ch02.ThetaRatio Q (1 / 2) (s / 3)
        data.toTriadicCoeffFamily ≤ B ^ (2 : ℕ) := by
  have hepscap := aux_inputs_deterministic_excess_chapter2Error_cap_six
    d data Q (s := s) (alpha := alpha) (B := Cerr * epsilon)
    hs halpha (mul_nonneg hCerr.le hepsilon.1.le) hpaper
  have hcap : Homogenization.Book.Ch02.HomogenizationErrorOnCube Q (s / 6)
      .infinity (.finite 2) data.toTriadicCoeffFamily
      (Homogenization.scalarMatrix (d := d) alpha) ≤ Cerr := by
    calc
      Homogenization.Book.Ch02.HomogenizationErrorOnCube Q (s / 6)
          .infinity (.finite 2) data.toTriadicCoeffFamily
          (Homogenization.scalarMatrix (d := d) alpha) ≤ Cerr * epsilon := hepscap
      _ ≤ Cerr := by
        calc
          Cerr * epsilon ≤ Cerr * 1 := mul_le_mul_of_nonneg_left hepsilon.2 hCerr.le
          _ = Cerr := mul_one _
  exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.localBoundaryEllipticityCaps_of_errorCap
    Q data.toTriadicCoeffFamily hs hs4 halpha hcap

/-- Large-gap branch of the original-power one-step excess estimate for a scalar coefficient, given the
boundary comparison of the harmonic replacement at the tuple (`aux_inputs_det_excess_large_gap_Cmp`, constant
`CAb`).  It is `inputs_det_excess_large_gap`, the boundary Schauder comparison of the manuscript proof of
`l.excess.decay.good.scales.GMC`. -/
theorem aux_inputs_deterministic_excess_large_gap
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (Cerr : ℝ) (hCerr : 0 < Cerr)
    (CAb : ℝ) (hCAb : 0 < CAb) :
    ∃ C : ℝ, 0 < C ∧
      3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) ≤ C ∧
      ∀ s : ℝ, 0 < s → s ≤ (1 / 4 : ℝ) →
      ∀ epsilon ∈ Set.Ioc (0 : ℝ) 1, ∀ k : ℕ, 6 ≤ k → 0 < k →
      ∀ m n : ℕ, k ≤ n → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      ∀ a : Vec d → ℝ, ∀ data : ScalarTriadicCoeffData (fun y => a (y + z)),
      ∀ a0 : ℝ, 0 < a0 →
      let err : ENNReal :=
        paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
          Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily a0;
      err ≤ ENNReal.ofReal (Cerr * epsilon) →
      Homogenization.Book.Ch02.HomogenizationErrorOnCube
          (originCube d ((n : ℤ) + 2)) (s / 6) .infinity (.finite 2)
          data.toTriadicCoeffFamily (Homogenization.scalarMatrix (d := d) a0) ≤
        Cerr * epsilon →
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn a (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemHolder (cube d m) (1 / 2) h.grad →
        aux_inputs_det_excess_large_gap_Cmp d CAb s m n z x a data a0 u h g →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        excess (n - k) (truncatedCube d m (n - k) x) u.toFun ≤
          C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon) *
              excess n (truncatedCube d m n x) u.toFun +
            C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) *
              err.toReal *
              (Real.sqrt (vecNormSq ell.slope) +
                (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                  s ^ (-3 / 2 : ℝ) *
                    Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                else 0)) +
            C * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
              (a0)⁻¹ * (3 : ℝ) ^ (s * n) *
              (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
            (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              C * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
              (3 : ℝ) ^ ((n : ℝ) / 2) *
                holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
            else 0) := by
  exact inputs_det_excess_large_gap d hd Cerr hCerr CAb hCAb

/-- The arbitrary-coefficient one-step excess estimate, CONDITIONAL on the boundary comparison at the
tuple (`aux_inputs_det_excess_large_gap_Cmp`, constant `CAb`): small gaps need no comparison, large gaps use it
once.  This is the deterministic part of `l.excess.decay.good.scales.GMC`; the cutoff-field instance is
`inputs_deterministic_excess`. -/
theorem aux_inputs_deterministic_excess_of_comparison (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∀ Cerr : ℝ, 0 < Cerr → ∀ CAb : ℝ, 0 < CAb → ∃ C : ℝ, 0 < C ∧
      ∀ s : ℝ, 0 < s → s ≤ (1 / 4 : ℝ) →
      ∀ epsilon ∈ Set.Ioc (0 : ℝ) 1, ∀ k : ℕ, 0 < k →
      ∀ m n : ℕ, k ≤ n → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      ∀ a : Vec d → ℝ, ∀ data : ScalarTriadicCoeffData (fun y => a (y + z)),
      ∀ a0 : ℝ, 0 < a0 →
      let err : ENNReal :=
        paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
          Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily a0;
      err ≤ ENNReal.ofReal (Cerr * epsilon) →
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn a (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemHolder (cube d m) (1 / 2) h.grad →
        aux_inputs_det_excess_large_gap_Cmp d CAb s m n z x a data a0 u h g →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        excess (n - k) (truncatedCube d m (n - k) x) u.toFun ≤
          C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon) *
              excess n (truncatedCube d m n x) u.toFun +
            C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) *
              err.toReal *
              (Real.sqrt (vecNormSq ell.slope) +
                (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                  s ^ (-3 / 2 : ℝ) *
                    Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                else 0)) +
            C * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
              (a0)⁻¹ *
              (3 : ℝ) ^ (s * n) *
              (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
            (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              C * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
              (3 : ℝ) ^ ((n : ℝ) / 2) *
                holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
            else 0)) := by
  intro Cerr hCerr CAb hCAb
  obtain ⟨C, hCpos, hKC, hlarge⟩ :=
    aux_inputs_deterministic_excess_large_gap d hd Cerr hCerr CAb hCAb
  refine ⟨C, hCpos, ?_⟩
  intro s hs hs4 epsilon heps k hk m n hkn hnm x hx z hz hxz a data a0 ha0
    errTerm hErr u h g hdir hg hholder hcmp ell hell
  by_cases hk6 : k < 6
  · let K : ℝ := 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))
    let D : ℝ := (3 : ℝ) ^ (-(k : ℝ) / 2)
    let q : ℝ := (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
      s ^ (-3 / 2 : ℝ) * epsilon
    let E : ℝ := excess n (truncatedCube d m n x) u.toFun
    let R₂ : ℝ := C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) *
      errTerm.toReal *
        (Real.sqrt (vecNormSq ell.slope) +
          (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
            s ^ (-3 / 2 : ℝ) *
              Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
          else 0))
    let R₃ : ℝ := C * s ^ (-15 / 2 : ℝ) *
      (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * (a0)⁻¹ *
      (3 : ℝ) ^ (s * n) *
      (fractionalSeminormOn (truncatedCube d m n x) s g).toReal
    let R₄ : ℝ :=
      if BoundaryTouches (truncatedCube d m n x) (cube d m) then
        C * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (3 : ℝ) ^ ((n : ℝ) / 2) *
            holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
      else 0
    have hK0 : 0 ≤ K := by positivity
    have hD0 : 0 ≤ D := by dsimp [D]; positivity
    have hq0 : 0 ≤ q := by
      dsimp [q]
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hs.le _))
        heps.1.le
    have hE0 : 0 ≤ E := by
      dsimp [E]
      exact SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.excess_nonneg _ _ _
    have hR20 : 0 ≤ R₂ := by
      dsimp [R₂]
      have hbracket : 0 ≤ Real.sqrt (vecNormSq ell.slope) +
          (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
            s ^ (-3 / 2 : ℝ) *
              Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
          else 0) := by
        split_ifs <;> positivity
      have herr0 : 0 ≤ errTerm.toReal := ENNReal.toReal_nonneg
      positivity
    have hR30 : 0 ≤ R₃ := by
      dsimp [R₃]
      have hsemi : 0 ≤ (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
        ENNReal.toReal_nonneg
      positivity
    have hR40 : 0 ≤ R₄ := by
      dsimp [R₄]
      split_ifs with hbt
      · exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (le_of_lt hCpos)
                (Real.rpow_nonneg hs.le _))
              (Real.rpow_nonneg (by norm_num) _))
            (Real.rpow_nonneg (by norm_num) _))
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.holderSeminormOn_nonneg
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.memHolder_mono hholder
              (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.truncatedCube_subset_cube
                d (m : ℤ) (n : ℤ) x)))
      · exact le_rfl
    have hsmall := aux_inputs_deterministic_excess_small_gap
      d hx hnm hkn hk6 u
    have hnum := aux_inputs_deterministic_excess_small_gap_rhs
      hKC (le_of_lt hCpos) hD0 hq0 hE0 hR20 hR30 hR40 hsmall
    simpa [K, D, q, E, R₂, R₃, R₄] using hnum
  · have hklarge : 6 ≤ k := by omega
    have hlocalErrorCap := aux_inputs_deterministic_excess_chapter2Error_cap_six
      d data (originCube d ((n : ℤ) + 2)) (s := s) (alpha := a0)
      (B := Cerr * epsilon) hs ha0
      (mul_nonneg hCerr.le heps.1.le) hErr
    exact hlarge s hs hs4 epsilon heps k hklarge hk m n hkn hnm x hx z hz hxz
      a data a0 ha0 hErr hlocalErrorCap u h g hdir hg hholder hcmp ell hell


/-- Clause 3 of the deterministic good-scale input in the paper's own form
(`l.excess.decay.good.scales.GMC`): the cutoff field on the good event `G_{n+2,z}(ε,s/8)`.  It is the
arbitrary-coefficient estimate `aux_inputs_deterministic_excess_of_comparison` applied to
`a = aCutoff M L ω` with the certificate `aCutoffTriadicData` of the translated sample and the boundary
comparison supplied by clause 1 (`inputs_deterministic_boundary`) on the same good event. -/
theorem inputs_deterministic_excess (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ epsilon ∈ Set.Icc (8 * s⁻¹ * M.delta ^ 2) 1, ∀ k : ℕ, 0 < k →
      ∀ L m n : ℕ, k ≤ n → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemHolder (cube d m) (1 / 2) h.grad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        indicatorValue (goodEvent M (some L) (n + 2) z epsilon (s / 8))
              (fun _ => excess (n - k) (truncatedCube d m (n - k) x) u.toFun) ω ≤
            C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon) *
                excess n (truncatedCube d m n x) u.toFun +
              C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) *
                section6HomogenizationError M (s / 8) L (n + 2) ω z *
                (Real.sqrt (vecNormSq ell.slope) +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) *
                      Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                  else 0)) +
              C * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                (3 : ℝ) ^ (s * n) *
                (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
              (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                C * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (3 : ℝ) ^ ((n : ℝ) / 2) *
                  holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
              else 0)) := by
  obtain ⟨Cerr, hCerr, hcut⟩ := _root_.SubdiffusiveProcess.Section6.cutoff_regularity_good_scales d
  obtain ⟨CAb, hCAb, hcl1⟩ := inputs_deterministic_boundary d hd
  obtain ⟨C, hC, hdet⟩ := aux_inputs_deterministic_excess_of_comparison d hd Cerr hCerr CAb hCAb
  refine ⟨C, hC, ?_⟩
  intro M s hs epsilon heps k hk L m n hkn hnm x hx z hz hxz ω u h g hsol hsOrder hholder ell hell
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdelta2 : 0 < M.delta ^ 2 := pow_pos hdelta 2
  have hs0 : 0 < s := (mul_pos (by norm_num) hdelta2).trans_le hs.1
  have heps0 : 0 < epsilon := by
    have hinv : 0 < s⁻¹ := inv_pos.mpr hs0
    exact lt_of_lt_of_le (mul_pos (mul_pos (by norm_num) hinv) hdelta2) heps.1
  have hepsIoc : epsilon ∈ Set.Ioc (0 : ℝ) 1 := ⟨heps0, heps.2⟩
  have hs8 : s / 8 ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ) := by
    constructor <;> nlinarith [hs.1, hs.2]
  have heps8 : epsilon ∈ Set.Icc ((s / 8)⁻¹ * M.delta ^ 2) 1 := by
    constructor
    · have hscale : (s / 8)⁻¹ * M.delta ^ 2 = 8 * s⁻¹ * M.delta ^ 2 := by
        field_simp [ne_of_gt hs0]
      rw [hscale]
      exact heps.1
    · exact heps.2
  let shiftedω := translatePotentialSample z ω
  let a0 : ℝ := tailAverage M L (n + 2) ω (translatedCube d (n + 2 : ℤ) z)
  have hcoeff : _root_.SubdiffusiveProcess.Model.aCutoff M L shiftedω =
      (fun y : Vec d => _root_.SubdiffusiveProcess.Model.aCutoff M L ω (y + z)) := by
    funext y
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.aCutoff_translatePotentialSample M L z ω y
  let data : ScalarTriadicCoeffData
      (fun y : Vec d => _root_.SubdiffusiveProcess.Model.aCutoff M L ω (y + z)) :=
    hcoeff ▸ aCutoffTriadicData M L shiftedω
  have hfamily : data.toTriadicCoeffFamily = aCutoffFamily M L shiftedω := by
    dsimp [data, aCutoffFamily]
    congr 1
  have ha0 : 0 < a0 := by
    have hpos := tailCoefficientCubeAverage_pos M L (n + 2) shiftedω
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at hpos
    simpa [a0] using hpos
  have ha0eq : a0 = tailCoefficientCubeAverage M L (n + 2) shiftedω := by
    dsimp [a0]
    exact (SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample
      M L (n + 2) z ω).symm
  have hMemHW : MemHolder (truncatedCube d m n x) (1 / 2) h.grad :=
    memHolder_mono hholder (truncatedCube_subset_cube d m n x)
  have hHolder : 0 ≤ holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad :=
    holderSeminormOn_nonneg hMemHW
  have hExcess : 0 ≤ excess n (truncatedCube d m n x) u.toFun := excess_nonneg _ _ _
  have hErr : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) ω z := ENNReal.toReal_nonneg
  have hTail : 0 ≤ (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ :=
    inv_nonneg.2 (tailAverage_nonneg M L (n + 2) ω _)
  have hFrac : 0 ≤ (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
    ENNReal.toReal_nonneg
  by_cases hgood : ω ∈ goodEvent M (some L) (n + 2) z epsilon (s / 8)
  · have hcapInd := ((hcut M L).2.2.2.2 (s / 8) hs8 epsilon heps8 (n + 2) z ω).2
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.indicatorValue_of_mem hgood] at hcapInd
    have hcap : section6HomogenizationError M (s / 8) L (n + 2) ω z ≤ Cerr * epsilon := hcapInd
    have herrEq : paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2)
          (s / 8) .infinity (.finite 2) data.toTriadicCoeffFamily a0 =
        ENNReal.ofReal (section6HomogenizationError M (s / 8) L (n + 2) ω z) := by
      rw [hfamily, ha0eq]
      exact SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.paperHomogenizationError_eq_ofReal_cutoffGoodEvent
        M (by nlinarith [hs.1]) (by nlinarith [hs.2]) L (n + 2) ω z heps0.le heps.2 hgood
    have herrBound : paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2)
          (s / 8) .infinity (.finite 2) data.toTriadicCoeffFamily a0 ≤
        ENNReal.ofReal (Cerr * epsilon) := by
      rw [herrEq]
      exact ENNReal.ofReal_le_ofReal hcap
    have herrReal : (paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2)
          (s / 8) .infinity (.finite 2) data.toTriadicCoeffFamily a0).toReal =
        section6HomogenizationError M (s / 8) L (n + 2) ω z := by
      rw [herrEq]
      exact ENNReal.toReal_ofReal ENNReal.toReal_nonneg
    -- the boundary comparison of clause 1 at this tuple, on the good event `G(1, s/8) ⊇ G(ε, s/8)`
    have hd1 : 1 ≤ d := by omega
    have hgood1 : ω ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) :=
      goodEvent_subset_one M (some L) (n + 2) z
        heps0.le heps.2 hgood
    have hMemFrac : MemFractionalOn (cube d m) s h.grad :=
      Section6ExcessDecay.memFractionalOn_cube_of_memHolder hd1 hs0 hs.2 hholder
    have hcmp : aux_inputs_det_excess_large_gap_Cmp d CAb s m n z x
        (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) data a0 u h g := by
      intro y hy hy1 hy2 uD huDval huDgrad
      rcases hcl1 M s hs L m n hnm z hz x hxz ω u h g hsol hsOrder hMemFrac y hy hy1 hy2 uD
          huDval huDgrad with ⟨hex, huniq, hbound⟩
      refine ⟨hex, huniq, ?_⟩
      intro v hvharm hvzt
      have hb := hbound v hvharm hvzt
      rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.indicatorValue_of_mem hgood1] at hb
      rw [herrReal]
      simpa only [Nat.cast_add] using hb
    have hdetBound := hdet s hs0 hs.2 epsilon hepsIoc k hk m n hkn hnm x hx z hz hxz
      (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) data a0 ha0 herrBound u h g hsol hsOrder hholder hcmp
      ell hell
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.indicatorValue_of_mem hgood]
    rw [herrReal, ha0eq] at hdetBound
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample
      M L (n + 2) z ω] at hdetBound
    simpa only [Nat.cast_add, Nat.cast_ofNat] using! hdetBound
  · rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.indicatorValue_of_notMem hgood]
    positivity


end SubdiffusiveProcess.Paper
