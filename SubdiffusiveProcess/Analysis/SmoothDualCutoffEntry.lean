module

public import SubdiffusiveProcess.Analysis.SmoothDualComparison
public import SubdiffusiveProcess.Analysis.SmoothDualLocalErrorLoop
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffSharpLoop

@[expose] public section

/-!
# K-free flat-comparator cutoff entry

Smooth-dual twins of the flat-comparator local error loop and of the sharp
good-event loop.  The upstream carrier `flatComparatorLocalCoarseBound`
carries a leading `(ofReal s)^(-1/2)` that comes from converting the library
smooth dual to the paper dual; the smooth-dual endpoint
`exists_cubeLpNorm_sub_le_of_localCoarseGrainingLpRHS_smoothDual` does not
need it.  Everything else, in particular the library right-hand side's own
`s⁻¹` and `s^(-9/2)`, is kept verbatim.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SmoothDualScratch

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open scoped ENNReal

noncomputable section

/-! ### Target 1: the K-free local coarse budget -/

/-- The local coarse budget of `flatComparatorLocalCoarseBound` without its
leading `(ofReal s)^(-1/2)`.  The two inner order powers `s⁻¹` and
`s^(-9/2)` are those of the library right-hand side
`localCoarseGrainingLpRHS`. -/
noncomputable def flatComparatorSmoothLocalCoarseBound
    (C : ℝ≥0∞) (sigma : ℝ) (s s1 s2 : FractionalOrder)
    (E1 E2 S D : ℝ) (n : ℤ) : ℝ≥0∞ :=
  C * (ENNReal.ofReal s.1)⁻¹ * (ENNReal.ofReal sigma) ^ (1 / 2 : ℝ) *
      (ENNReal.ofReal (Real.rpow 3 s1.1) * ENNReal.ofReal E1) *
      ENNReal.ofReal S +
    C * (ENNReal.ofReal s.1) ^ (-(9 / 2 : ℝ)) *
      (ENNReal.ofReal (s2.1 - s.1))⁻¹ *
      (1 + (ENNReal.ofReal (Real.rpow 3 (s1.1 / 2)) *
        ENNReal.ofReal E2) ^ 2) *
      ENNReal.ofReal (Real.rpow 3 (s2.1 * (n : ℝ))) * ENNReal.ofReal D

/-- The upstream budget is exactly `(ofReal s)^(-1/2)` times the K-free one. -/
theorem flatComparatorLocalCoarseBound_eq_rpow_mul_smooth
    (C : ℝ≥0∞) (sigma : ℝ) (s s1 s2 : FractionalOrder)
    (E1 E2 S D : ℝ) (n : ℤ) :
    flatComparatorLocalCoarseBound C sigma s s1 s2 E1 E2 S D n =
      (ENNReal.ofReal s.1) ^ (-(1 / 2 : ℝ)) *
        flatComparatorSmoothLocalCoarseBound C sigma s s1 s2 E1 E2 S D n := by exact SubdiffusiveProcess.SmoothDualComparison.flatComparatorLocalCoarseBound_eq_rpow_mul_smooth (C := C) (sigma := sigma) (s := s) (s1 := s1) (s2 := s2) (E1 := E1) (E2 := E2) (S := S) (D := D) (n := n)

theorem flatComparatorSmoothLocalCoarseBound_lt_top
    {C : ℝ≥0∞} (hC : C < ∞) (sigma : ℝ) (s s1 s2 : FractionalOrder)
    (hss2 : s.1 < s2.1) (E1 E2 S D : ℝ) (n : ℤ) :
    flatComparatorSmoothLocalCoarseBound C sigma s s1 s2 E1 E2 S D n < ∞ := by exact SubdiffusiveProcess.SmoothDualComparison.flatComparatorSmoothLocalCoarseBound_lt_top (C := C) (hC := hC) (sigma := sigma) (s := s) (s1 := s1) (s2 := s2) (hss2 := hss2) (E1 := E1) (E2 := E2) (S := S) (D := D) (n := n)

/-- Monotone replacement of the four local finite-`p` slots by real bounds,
with no leading order factor on the left. -/
theorem localCoarseGrainingLpRHS_le_flatComparatorSmoothLocalCoarseBound
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d)
    (C : ℝ≥0∞) (sigma : ℝ) (hsigma : 0 < sigma)
    (g : Vec d → Vec d) (u : H1Function (openCubeSet Q))
    (s1 s s2 : FractionalOrder) (E1 E2 S D : ℝ)
    (hE1 : Ch02.HomogenizationErrorOnCube Q s1.1 .infinity (.finite 1) A
      (scalarMatrix (d := d) sigma) ≤ E1)
    (hE2 : Ch02.HomogenizationErrorOnCube Q (s1.1 / 2) .infinity (.finite 2) A
      (scalarMatrix (d := d) sigma) ≤ E2)
    (hS : weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
      (A.coeffOn Q) u s1 s FiniteLpExponent.two ≤ ENNReal.ofReal S)
    (hD : ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
      FiniteLpExponent.two g ≤ ENNReal.ofReal D) :
    localCoarseGrainingLpRHS C Q (Q.scale - 1) (by omega)
        (A.coeffOn Q) sigma hsigma g u s1 s s2 FiniteLpExponent.two ≤
      flatComparatorSmoothLocalCoarseBound C sigma s s1 s2 E1 E2 S D
        (Q.scale - 1) := by
  have hE10 : ENNReal.ofReal
      (Ch02.HomogenizationErrorOnCube Q s1.1 .infinity (.finite 1) A
        (scalarMatrix (d := d) sigma)) ≤ ENNReal.ofReal E1 :=
    ENNReal.ofReal_le_ofReal hE1
  have hE20 : ENNReal.ofReal
      (Ch02.HomogenizationErrorOnCube Q (s1.1 / 2) .infinity (.finite 2) A
        (scalarMatrix (d := d) sigma)) ≤ ENNReal.ofReal E2 :=
    ENNReal.ofReal_le_ofReal hE2
  have hp1 := parentTruncatedErrorOne_sub_one_le_localError Q A sigma hsigma s1
  have hp2 := parentTruncatedErrorTwo_sub_one_le_localError Q A sigma hsigma
    (fractionalOrderHalf s1)
  have hp1' : Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q
      (Q.scale - 1) (by omega) (A.coeffOn Q) sigma hsigma s1 ≤
      ENNReal.ofReal (Real.rpow 3 s1.1) * ENNReal.ofReal E1 :=
    hp1.trans (mul_le_mul_right hE10 _)
  have hp2' : Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q
      (Q.scale - 1) (by omega) (A.coeffOn Q) sigma hsigma
        (fractionalOrderHalf s1) ≤
      ENNReal.ofReal (Real.rpow 3 (s1.1 / 2)) * ENNReal.ofReal E2 := by
    simpa [fractionalOrderHalf] using hp2.trans (mul_le_mul_right hE20 _)
  unfold localCoarseGrainingLpRHS flatComparatorSmoothLocalCoarseBound
  gcongr

/-- Real readout of the K-free budget: exactly the library's inner powers
`s⁻¹` and `s^(-9/2)`, with no outer `s^(-1/2)`. -/
theorem flatComparatorSmoothLocalCoarseBound_toReal_le
    (C : ℝ≥0∞) (sigma : ℝ) (s s1 s2 : FractionalOrder)
    (E1 E2 S D : ℝ) (n : ℤ)
    (hss2 : s.1 < s2.1)
    (hsigma : 0 < sigma) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (hS : 0 ≤ S) (hD : 0 ≤ D) :
    (flatComparatorSmoothLocalCoarseBound C sigma s s1 s2 E1 E2 S D n).toReal ≤
      C.toReal * s.1⁻¹ * Real.sqrt sigma * Real.rpow 3 s1.1 * E1 * S +
        C.toReal * Real.rpow s.1 (-(9 / 2 : ℝ)) *
          (s2.1 - s.1)⁻¹ *
          (1 + (Real.rpow 3 (s1.1 / 2) * E2) ^ 2) *
          Real.rpow 3 (s2.1 * (n : ℝ)) * D := by exact SubdiffusiveProcess.SmoothDualComparison.flatComparatorSmoothLocalCoarseBound_toReal_le (C := C) (sigma := sigma) (s := s) (s1 := s1) (s2 := s2) (E1 := E1) (E2 := E2) (S := S) (D := D) (n := n) (hss2 := hss2) (hsigma := hsigma) (hE1 := hE1) (hE2 := hE2) (hS := hS) (hD := hD)

/-! ### Target 2: the smooth-dual local error loop and its manuscript form -/

/-- Complete smooth-dual local error loop: one-scale tail, finite-`p` coarse
graining in the smooth dual, and the uniform smooth-dual readout.  Twin of
`exists_cubeLpNorm_sub_le_flatComparatorLocalCoarseBound_sharp`. -/
theorem exists_cubeLpNorm_sub_le_flatComparatorSmoothLocalCoarseBound
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (s1 s s2 : FractionalOrder), s1.1 < s.1 → s.1 < s2.1 →
        s.1 ≤ 1 / 4 →
      ∀ (A : Ch02.TriadicCoeffFamily d) (sigma : ℝ) (_hsigma : 0 < sigma)
        (g : Vec d → Vec d),
        MemCubeEuclideanFullWsp (originCube d m) s2 FiniteLpExponent.two g →
      ∀ u v : H1Function (openCubeSet (originCube d m)),
        IsForcedEquation (originCube d m) (A.coeffOn (originCube d m)) u g →
        IsScalarForcedEquation (originCube d m) sigma v g →
        HasH10Difference (originCube d m) u v →
      ∀ E1 E2 S D : ℝ,
        Ch02.HomogenizationErrorOnCube (originCube d m) s1.1 .infinity (.finite 1) A
          (scalarMatrix (d := d) sigma) ≤ E1 →
        Ch02.HomogenizationErrorOnCube (originCube d m) (s1.1 / 2)
          .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤ E2 →
        weightedLocalSymmetricEnergyLp (originCube d m) (m - 1) (by simp [originCube])
          (A.coeffOn (originCube d m)) u s1 s FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        cubeLpNorm (originCube d m) 2 (fun x => u.toFun x - v.toFun x) ≤
          (UniformSmoothReadout.uniformSmoothDualReadoutConstant d *
            ENNReal.ofReal (centeredCubeScale m * sigma⁻¹ *
              (flatComparatorSmoothLocalCoarseBound C sigma s s1 s2 E1 E2 S D
                (m - 1)).toReal)).toReal := by
  obtain ⟨C, hCtop, hmain⟩ :=
    exists_cubeLpNorm_sub_le_of_localCoarseGrainingLpRHS_smoothDual d hd
  refine ⟨C, hCtop, ?_⟩
  intro m s1 s s2 hs1s hss2 hs A sigma hsigma g hg u v hu hv huv
    E1 E2 S D hE1 hE2 hS hD
  let B := flatComparatorSmoothLocalCoarseBound C sigma s s1 s2 E1 E2 S D (m - 1)
  have hBtop : B < ∞ :=
    flatComparatorSmoothLocalCoarseBound_lt_top hCtop _ _ _ _ hss2 _ _ _ _ _
  have hB0 : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  apply hmain m (m - 1) (by omega) s1 s s2 hs1s hss2 hs
    (A.coeffOn (originCube d m)) sigma hsigma g hg u v hu hv huv B.toReal hB0
  rw [ENNReal.ofReal_toReal hBtop.ne]
  exact localCoarseGrainingLpRHS_le_flatComparatorSmoothLocalCoarseBound
    (originCube d m) A C sigma hsigma g u s1 s s2 E1 E2 S D hE1 hE2
      (by simpa [originCube] using hS) hD

/-- Manuscript specialization at `(s₁,s,s₂)=(t/3,t/2,t)` of the smooth-dual
loop.  Twin of `exists_cubeLpNorm_sub_le_flatComparatorManuscriptBound_sharp`. -/
theorem exists_cubeLpNorm_sub_le_flatComparatorSmoothManuscriptBound
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (htQuarter : t ≤ 1 / 4)
        (A : Ch02.TriadicCoeffFamily d) (sigma : ℝ) (_hsigma : 0 < sigma)
        (g : Vec d → Vec d),
      let s1 : FractionalOrder := ⟨t / 3, by positivity, by linarith⟩
      let smid : FractionalOrder := ⟨t / 2, by positivity, by linarith⟩
      let s2 : FractionalOrder := ⟨t, ht, ht1⟩
      MemCubeEuclideanFullWsp (originCube d m) s2 FiniteLpExponent.two g →
      ∀ u v : H1Function (openCubeSet (originCube d m)),
        IsForcedEquation (originCube d m) (A.coeffOn (originCube d m)) u g →
        IsScalarForcedEquation (originCube d m) sigma v g →
        HasH10Difference (originCube d m) u v →
      ∀ E S D : ℝ,
        Ch02.HomogenizationErrorOnCube (originCube d m) (t / 6)
          .infinity (.finite 2) A (scalarMatrix (d := d) sigma) ≤ E →
        weightedLocalSymmetricEnergyLp (originCube d m) (m - 1) (by simp [originCube])
          (A.coeffOn (originCube d m)) u s1 smid FiniteLpExponent.two ≤
            ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        cubeLpNorm (originCube d m) 2 (fun x => u.toFun x - v.toFun x) ≤
          (UniformSmoothReadout.uniformSmoothDualReadoutConstant d *
            ENNReal.ofReal (centeredCubeScale m * sigma⁻¹ *
              (flatComparatorSmoothLocalCoarseBound C sigma smid s1 s2 E E S D
                (m - 1)).toReal)).toReal := by
  obtain ⟨C, hCtop, hmain⟩ :=
    exists_cubeLpNorm_sub_le_flatComparatorSmoothLocalCoarseBound d hd
  refine ⟨C, hCtop, ?_⟩
  intro m t ht ht1 htQuarter A sigma hsigma g
  dsimp only
  intro hg u v hu hv huv E S D hE hS hD
  let s1 : FractionalOrder := ⟨t / 3, by positivity, by linarith⟩
  let smid : FractionalOrder := ⟨t / 2, by positivity, by linarith⟩
  let s2 : FractionalOrder := ⟨t, ht, ht1⟩
  have hE1 : Ch02.HomogenizationErrorOnCube (originCube d m) s1.1 .infinity
      (.finite 1) A (scalarMatrix (d := d) sigma) ≤ E := by
    have hcomp := homogenizationError_infinity_one_le_two_half
      (originCube d m) A (scalarMatrix (d := d) sigma)
      (u := s1.1) (by dsimp [s1]; positivity)
    have hsix : s1.1 / 2 = t / 6 := by dsimp [s1]; ring
    rw [hsix] at hcomp
    exact hcomp.trans hE
  apply hmain m s1 smid s2
    (by dsimp [s1, smid]; linarith) (by dsimp [smid, s2]; linarith)
    (by dsimp [smid]; linarith) A sigma hsigma g hg u v hu hv huv
      E E S D hE1
  · have heq : t / 3 / 2 = t / 6 := by ring
    simpa only [s1, heq] using hE
  · exact hS
  · exact hD

/-! ### Target 3: the K-free good-event loop carrier and its real readout -/

/-- Scalar carrier of the smooth-dual good-event comparator loop.  Twin of
`flatComparatorSharpGoodEventLoopBound` with the K-free budget and the
uniform smooth-dual readout constant. -/
noncomputable def flatComparatorSmoothGoodEventLoopBound
    (C : ℝ≥0∞) (d : ℕ) [NeZero d] (n : ℕ) (sigma : ℝ)
    (smid s1 s2 : FractionalOrder) (E S D : ℝ)
    (Q : TriadicCube d) (g : Vec d → Vec d) : ℝ :=
  (UniformSmoothReadout.uniformSmoothDualReadoutConstant d *
      ENNReal.ofReal (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
        (flatComparatorSmoothLocalCoarseBound C sigma smid s1 s2 E E S D
          ((n : ℤ) - 3)).toReal)).toReal +
    unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) *
      (d : ℝ) * sigma⁻¹ *
        (Real.sqrt (Fintype.card (Fin d) : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q smid.1 g)

/-- Real-valued readout of the smooth-dual loop.  Twin of
`flatComparatorSharpGoodEventLoopBound_le_realReadout` with the leading
`smid^(-1/2)` absent and every other factor unchanged. -/
theorem flatComparatorSmoothGoodEventLoopBound_le_realReadout
    (C : ℝ≥0∞) (d n : ℕ) [NeZero d] (sigma : ℝ)
    (smid s1 s2 : FractionalOrder) (E S D : ℝ)
    (Q : TriadicCube d) (g : Vec d → Vec d)
    (hmid2 : smid.1 < s2.1) (hsigma : 0 < sigma)
    (hE : 0 ≤ E) (hS : 0 ≤ S) (hD : 0 ≤ D) :
    flatComparatorSmoothGoodEventLoopBound C d n sigma smid s1 s2 E S D Q g ≤
      (UniformSmoothReadout.uniformSmoothDualReadoutConstant d).toReal *
        centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
          (C.toReal * smid.1⁻¹ * Real.sqrt sigma *
              Real.rpow 3 s1.1 * E * S +
            C.toReal * Real.rpow smid.1 (-(9 / 2 : ℝ)) *
              (s2.1 - smid.1)⁻¹ *
              (1 + (Real.rpow 3 (s1.1 / 2) * E) ^ 2) *
              Real.rpow 3 (s2.1 * (((n : ℤ) - 3 : ℤ) : ℝ)) * D) +
        unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) *
          (d : ℝ) * sigma⁻¹ *
            (Real.sqrt (Fintype.card (Fin d) : ℝ) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q smid.1 g) := by
  have hbudget := flatComparatorSmoothLocalCoarseBound_toReal_le
    C sigma smid s1 s2 E E S D ((n : ℤ) - 3)
      hmid2 hsigma hE hE hS hD
  have hscale : 0 ≤ centeredCubeScale ((n : ℤ) - 2) :=
    (centeredCubeScale_pos ((n : ℤ) - 2)).le
  have hinv : 0 ≤ sigma⁻¹ := inv_nonneg.mpr hsigma.le
  have hreal0 : 0 ≤ centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
      (flatComparatorSmoothLocalCoarseBound C sigma smid s1 s2 E E S D
        ((n : ℤ) - 3)).toReal := by positivity
  unfold flatComparatorSmoothGoodEventLoopBound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hreal0]
  let R : ℝ :=
    C.toReal * smid.1⁻¹ * Real.sqrt sigma * Real.rpow 3 s1.1 * E * S +
      C.toReal * Real.rpow smid.1 (-(9 / 2 : ℝ)) *
        (s2.1 - smid.1)⁻¹ *
        (1 + (Real.rpow 3 (s1.1 / 2) * E) ^ 2) *
        Real.rpow 3 (s2.1 * (((n : ℤ) - 3 : ℤ) : ℝ)) * D
  have hfirst :
      (UniformSmoothReadout.uniformSmoothDualReadoutConstant d).toReal *
          (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
            (flatComparatorSmoothLocalCoarseBound C sigma smid s1 s2 E E S D
              ((n : ℤ) - 3)).toReal) ≤
        (UniformSmoothReadout.uniformSmoothDualReadoutConstant d).toReal *
          centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ * R := by
    calc
      _ ≤ (UniformSmoothReadout.uniformSmoothDualReadoutConstant d).toReal *
          (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ * R) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by simpa only [R] using hbudget)
            (mul_nonneg hscale hinv)) ENNReal.toReal_nonneg
      _ = _ := by ring
  simpa only [R] using add_le_add hfirst (le_refl
    (unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) *
      (d : ℝ) * sigma⁻¹ *
        (Real.sqrt (Fintype.card (Fin d) : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q smid.1 g)))

/-- Old carrier dominates the new one up to the leading `smid^(-1/2)`:
with `smid ≤ 1` the K-free carrier is never larger than the sharp one. -/
theorem flatComparatorSmoothLocalCoarseBound_le_flatComparatorLocalCoarseBound
    (C : ℝ≥0∞) (sigma : ℝ) (s s1 s2 : FractionalOrder)
    (E1 E2 S D : ℝ) (n : ℤ) :
    flatComparatorSmoothLocalCoarseBound C sigma s s1 s2 E1 E2 S D n ≤
      flatComparatorLocalCoarseBound C sigma s s1 s2 E1 E2 S D n := by
  rw [flatComparatorLocalCoarseBound_eq_rpow_mul_smooth]
  have hs1 : ENNReal.ofReal s.1 ≤ 1 := by
    rw [ENNReal.ofReal_le_one]
    exact s.2.2.le
  have hone : 1 ≤ (ENNReal.ofReal s.1) ^ (-(1 / 2 : ℝ)) :=
    ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
      (ENNReal.ofReal_pos.2 s.2.1) hs1 (by norm_num)
  calc
    flatComparatorSmoothLocalCoarseBound C sigma s s1 s2 E1 E2 S D n =
        1 * flatComparatorSmoothLocalCoarseBound C sigma s s1 s2 E1 E2 S D n :=
      (one_mul _).symm
    _ ≤ _ := by gcongr

/-! ### Target 3 (companion): good-event twins of `FlatComparatorSharpErrorLoop`
lines 27–207 and of `Section6HolderBelowCutoff/CutoffSharpLoop.lean`, generated by
literal substitution of the K-free carriers and the smooth manuscript bound. -/

section GoodEventTwins

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

/-- Good-event specialization of the smooth-dual local comparator estimate. -/
theorem exists_cubeLpNorm_sub_le_flatComparatorGoodEventBound_smoothDual
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ) (_hnL : n + 2 ≤ L)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M none (n + 2) z 1 (s / 8)),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u v : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u g →
        IsScalarForcedEquation Q sigma v g →
        HasH10Difference Q u v →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        cubeLpNorm Q 2 (fun x => u.toFun x - v.toFun x) ≤
          (UniformSmoothReadout.uniformSmoothDualReadoutConstant d *
            ENNReal.ofReal (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
              (flatComparatorSmoothLocalCoarseBound C sigma smid s1 s2 E E S D
                ((n : ℤ) - 3)).toReal)).toReal := by
  obtain ⟨C, hCtop, hmain⟩ :=
    exists_cubeLpNorm_sub_le_flatComparatorSmoothManuscriptBound d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs L n hnL omega y z hcontain hgood
  dsimp only
  intro g hg u v hu hv huv S D hS hD
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hs1 : s < 1 := lt_of_le_of_lt hs.2 (by norm_num)
  let E := Real.sqrt (192 * (d : ℝ)) *
    ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
      section6HomogenizationError M (s / 8) L (n + 2) omega z)
  have hE := localHomogenizationError_two_le_anchor_of_closedContainment
    M hs L n hnL omega y z hcontain hgood
  have hres := hmain ((n : ℤ) - 2) s hs0 hs1 hs.2
    (aCutoffFamily M L (translatePotentialSample y omega))
    (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z))
    (by
      rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
      rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
      exact tailCoefficientCubeAverage_pos M L (n + 2)
        (translatePotentialSample z omega)) g hg u v hu hv huv E S D
    (by simpa only [E] using hE)
    (by simpa [originCube] using hS) hD
  simpa only [E, show ((n : ℤ) - 2) - 1 = (n : ℤ) - 3 by ring] using hres

/-- Complete smooth-dual local comparator loop, including the direct forcing
comparison to the unit harmonic function. -/
theorem exists_cubeLpNorm_sub_unitHarmonic_le_flatComparatorGoodEvent_smoothDual
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ) (_hnL : n + 2 ≤ L)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M none (n + 2) z 1 (s / 8)),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u v h : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u g →
        IsScalarForcedEquation Q sigma v g →
        HasH10Difference Q u v →
        IsUnitWeaklyHarmonicOn (openCubeSet Q) h →
        HasH10Difference Q u h →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        cubeLpNorm Q 2 (fun x ↦ u.toFun x - h.toFun x) ≤
          (UniformSmoothReadout.uniformSmoothDualReadoutConstant d *
            ENNReal.ofReal (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
              (flatComparatorSmoothLocalCoarseBound C sigma smid s1 s2 E E S D
                ((n : ℤ) - 3)).toReal)).toReal +
          unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) *
            (d : ℝ) * sigma⁻¹ *
              (Real.sqrt (Fintype.card (Fin d) : ℝ) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q smid.1 g) := by
  obtain ⟨C, hCtop, hcoarse⟩ :=
    exists_cubeLpNorm_sub_le_flatComparatorGoodEventBound_smoothDual d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs L n hnL omega y z hcontain hgood
  dsimp only
  intro g hg u v h hu hv huv hh huh S D hS hD
  let s1 : FractionalOrder := ⟨s / 3, by
    have hs0 : 0 < s :=
      (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
    positivity, by linarith [hs.2]⟩
  let smid : FractionalOrder := ⟨s / 2, by
    have hs0 : 0 < s :=
      (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
    positivity, by linarith [hs.2]⟩
  let s2 : FractionalOrder := ⟨s, by
    exact (mul_pos (by norm_num)
      (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
    by linarith [hs.2]⟩
  let E := Real.sqrt (192 * (d : ℝ)) *
    ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
      section6HomogenizationError M (s / 8) L (n + 2) omega z)
  have hcoarse' := hcoarse M s hs L n hnL omega y z hcontain hgood
    g hg u v hu hv huv S D (by simpa [s1, smid] using hS) hD
  have hreg : ForceBesovRegularity (originCube d ((n : ℤ) - 2)) smid.1 g := by
    apply forceBesovRegularity_of_memCubeEuclideanFullWsp_lt hg
    have hs0 : 0 < s :=
      (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
    dsimp [smid, s2]
    linarith
  have hvh : HasH10Difference (originCube d ((n : ℤ) - 2)) v h :=
    hasH10Difference_trans (hasH10Difference_symm huv) huh
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hforce := cubeLpNorm_scalarForced_sub_unitHarmonic_le_positiveBesov
    ((n : ℤ) - 2) hsigma hreg hv hh hvh
  exact cubeLpNorm_sub_unitHarmonic_le_add
    (originCube d ((n : ℤ) - 2)) u v h
    (by simpa only [E, s1, smid, s2] using hcoarse')
    (by simpa only [smid] using hforce)


/-- Cutoff good-event specialization of the smooth-dual local comparator estimate. -/
theorem exists_cubeLpNorm_sub_le_flatComparatorCutoffGoodEventBound_smoothDual
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8)),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u v : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u g →
        IsScalarForcedEquation Q sigma v g →
        HasH10Difference Q u v →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        cubeLpNorm Q 2 (fun x => u.toFun x - v.toFun x) ≤
          (UniformSmoothReadout.uniformSmoothDualReadoutConstant d *
            ENNReal.ofReal (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
              (flatComparatorSmoothLocalCoarseBound C sigma smid s1 s2 E E S D
                ((n : ℤ) - 3)).toReal)).toReal := by
  obtain ⟨C, hCtop, hmain⟩ :=
    exists_cubeLpNorm_sub_le_flatComparatorSmoothManuscriptBound d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs L n omega y z hcontain hgood
  dsimp only
  intro g hg u v hu hv huv S D hS hD
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hs1 : s < 1 := lt_of_le_of_lt hs.2 (by norm_num)
  let E := Real.sqrt (192 * (d : ℝ)) *
    ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
      section6HomogenizationError M (s / 8) L (n + 2) omega z)
  have hE := localHomogenizationError_two_le_cutoffAnchor_of_closedContainment
    M hs L n omega y z hcontain hgood
  have hres := hmain ((n : ℤ) - 2) s hs0 hs1 hs.2
    (aCutoffFamily M L (translatePotentialSample y omega))
    (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z))
    (by
      rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
      rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
      exact tailCoefficientCubeAverage_pos M L (n + 2)
        (translatePotentialSample z omega)) g hg u v hu hv huv E S D
    (by simpa only [E] using hE)
    (by simpa [originCube] using hS) hD
  simpa only [E, show ((n : ℤ) - 2) - 1 = (n : ℤ) - 3 by ring] using hres

/-- Complete smooth-dual local comparator loop at a finite cutoff, including the
direct forcing comparison to the unit harmonic function. -/
theorem exists_cubeLpNorm_sub_unitHarmonic_le_flatComparatorCutoffGoodEvent_smoothDual
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8)),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u v h : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u g →
        IsScalarForcedEquation Q sigma v g →
        HasH10Difference Q u v →
        IsUnitWeaklyHarmonicOn (openCubeSet Q) h →
        HasH10Difference Q u h →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        cubeLpNorm Q 2 (fun x ↦ u.toFun x - h.toFun x) ≤
          (UniformSmoothReadout.uniformSmoothDualReadoutConstant d *
            ENNReal.ofReal (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
              (flatComparatorSmoothLocalCoarseBound C sigma smid s1 s2 E E S D
                ((n : ℤ) - 3)).toReal)).toReal +
          unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) *
            (d : ℝ) * sigma⁻¹ *
              (Real.sqrt (Fintype.card (Fin d) : ℝ) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q smid.1 g) := by
  obtain ⟨C, hCtop, hcoarse⟩ :=
    exists_cubeLpNorm_sub_le_flatComparatorCutoffGoodEventBound_smoothDual d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs L n omega y z hcontain hgood
  dsimp only
  intro g hg u v h hu hv huv hh huh S D hS hD
  let s1 : FractionalOrder := ⟨s / 3, by
    have hs0 : 0 < s :=
      (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
    positivity, by linarith [hs.2]⟩
  let smid : FractionalOrder := ⟨s / 2, by
    have hs0 : 0 < s :=
      (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
    positivity, by linarith [hs.2]⟩
  let s2 : FractionalOrder := ⟨s, by
    exact (mul_pos (by norm_num)
      (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
    by linarith [hs.2]⟩
  let E := Real.sqrt (192 * (d : ℝ)) *
    ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
      section6HomogenizationError M (s / 8) L (n + 2) omega z)
  have hcoarse' := hcoarse M s hs L n omega y z hcontain hgood
    g hg u v hu hv huv S D (by simpa [s1, smid] using hS) hD
  have hreg : ForceBesovRegularity (originCube d ((n : ℤ) - 2)) smid.1 g := by
    apply forceBesovRegularity_of_memCubeEuclideanFullWsp_lt hg
    have hs0 : 0 < s :=
      (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
    dsimp [smid, s2]
    linarith
  have hvh : HasH10Difference (originCube d ((n : ℤ) - 2)) v h :=
    hasH10Difference_trans (hasH10Difference_symm huv) huh
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hforce := cubeLpNorm_scalarForced_sub_unitHarmonic_le_positiveBesov
    ((n : ℤ) - 2) hsigma hreg hv hh hvh
  exact cubeLpNorm_sub_unitHarmonic_le_add
    (originCube d ((n : ℤ) - 2)) u v h
    (by simpa only [E, s1, smid, s2] using hcoarse')
    (by simpa only [smid] using hforce)

/-- Arbitrary translated-cube physical-frame smooth-dual loop at a finite cutoff. -/
theorem exists_normalizedL2On_sub_flatComparator_le_cutoffGoodEventLoop_of_forced_smoothDual
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8)),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u0 : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u0 g →
      ∀ (uPhysical : Vec d → ℝ)
        (ubar : H1Function (translateSet y (openCubeSet Q))),
        IsUnitWeaklyHarmonicOn (translateSet y (openCubeSet Q)) ubar →
        MemH10 (translateSet y (openCubeSet Q))
          (fun p ↦ ubar.toFun p - uPhysical p) →
        (∀ p, u0.toFun p = uPhysical (p + y)) →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u0 s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        normalizedL2On (translateSet y (openCubeSet Q))
            (fun p ↦ uPhysical p - ubar.toFun p) ≤
          flatComparatorSmoothGoodEventLoopBound C d n sigma smid s1 s2
            E S D Q g := by
  obtain ⟨C, hCtop, hloop⟩ :=
    exists_cubeLpNorm_sub_unitHarmonic_le_flatComparatorCutoffGoodEvent_smoothDual d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs L n omega y z hcontain hgood
  dsimp only
  intro g hg u0 hu0 uPhysical ubar hh ht hu0Physical S D hS hD
  have hgTwo : MemLp g 2 (normalizedCubeMeasure (originCube d ((n : ℤ) - 2))) :=
    MemCubeEuclideanFullWsp.memLpTwo (by norm_num) hg
  have hgCube : MemVectorL2 (cubeSet (originCube d ((n : ℤ) - 2))) g :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure
      (originCube d ((n : ℤ) - 2)) hgTwo
  have hgOpen : MemVectorL2 (openCubeSet (originCube d ((n : ℤ) - 2))) g := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hgCube
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  let v0 := sourceForcedReplacement
    (scalarConstantCoeffMatrix (d := d) hsigma) u0 hgOpen
  have hv0 : IsScalarForcedEquation (originCube d ((n : ℤ) - 2))
      (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z)) v0 g :=
    isScalarForcedEquation_sourceForcedReplacement hsigma u0 hgOpen
  have huv0 : HasH10Difference (originCube d ((n : ℤ) - 2)) u0 v0 :=
    hasH10Difference_sourceForcedReplacement
      (scalarConstantCoeffMatrix (d := d) hsigma) u0 hgOpen
  obtain ⟨ubar0, hh0, hu0bar0, hnorm⟩ :=
    exists_recenteredFlatComparator (originCube d ((n : ℤ) - 2)) y
      u0 uPhysical ubar hh ht hu0Physical
  rw [hnorm]
  have hout := hloop M s hs L n omega y z hcontain hgood g hg u0 v0 ubar0
    hu0 hv0 huv0 hh0 hu0bar0 S D hS hD
  simpa only [flatComparatorSmoothGoodEventLoopBound] using hout

/-- The cutoff smooth-dual loop at the `[NeZero d]` signature of the Section 6
anchors. -/
theorem exists_normalizedL2On_sub_flatComparator_le_cutoffGoodEventLoop_of_forced_smoothDual_neZero
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8)),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u0 : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u0 g →
      ∀ (uPhysical : Vec d → ℝ)
        (ubar : H1Function (translateSet y (openCubeSet Q))),
        IsUnitWeaklyHarmonicOn (translateSet y (openCubeSet Q)) ubar →
        MemH10 (translateSet y (openCubeSet Q))
          (fun p ↦ ubar.toFun p - uPhysical p) →
        (∀ p, u0.toFun p = uPhysical (p + y)) →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u0 s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        normalizedL2On (translateSet y (openCubeSet Q))
            (fun p ↦ uPhysical p - ubar.toFun p) ≤
          flatComparatorSmoothGoodEventLoopBound C d n sigma smid s1 s2
            E S D Q g := by
  classical
  by_cases hmodel : Nonempty (SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
  · let M0 : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d := Classical.choice hmodel
    exact exists_normalizedL2On_sub_flatComparator_le_cutoffGoodEventLoop_of_forced_smoothDual
      d M0.shellPrefix.dimension
  · refine ⟨0, ENNReal.zero_lt_top, ?_⟩
    intro M
    exact (hmodel ⟨M⟩).elim


end GoodEventTwins

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SmoothDualScratch
