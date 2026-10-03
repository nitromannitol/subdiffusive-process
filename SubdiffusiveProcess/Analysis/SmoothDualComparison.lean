module

public import SubdiffusiveProcess.Analysis.SmoothDualLocalErrorLoop
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffSharpLoop

@[expose] public section

/-!
# Smooth-dual comparison for arbitrary coefficient families

Smooth-dual twins of the flat-comparator local error loop and of the sharp
good-event loop.  The upstream carrier `flatComparatorLocalCoarseBound`
carries a leading `(ofReal s)^(-1/2)` that comes from converting the library
smooth dual to the paper dual; the smooth-dual endpoint
`exists_cubeLpNorm_sub_le_of_localCoarseGrainingLpRHS_smoothDual` does not
need it.  Everything else, in particular the library right-hand side's own
`s⁻¹` and `s^(-9/2)`, is kept verbatim.
-/

namespace SubdiffusiveProcess.SmoothDualComparison

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SmoothDualScratch
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
        flatComparatorSmoothLocalCoarseBound C sigma s s1 s2 E1 E2 S D n :=
  rfl

theorem flatComparatorSmoothLocalCoarseBound_lt_top
    {C : ℝ≥0∞} (hC : C < ∞) (sigma : ℝ) (s s1 s2 : FractionalOrder)
    (hss2 : s.1 < s2.1) (E1 E2 S D : ℝ) (n : ℤ) :
    flatComparatorSmoothLocalCoarseBound C sigma s s1 s2 E1 E2 S D n < ∞ := by
  unfold flatComparatorSmoothLocalCoarseBound
  have hs0 : 0 < ENNReal.ofReal s.1 := ENNReal.ofReal_pos.2 s.2.1
  have hgap0 : 0 < ENNReal.ofReal (s2.1 - s.1) :=
    ENNReal.ofReal_pos.2 (sub_pos.mpr hss2)
  have hsInv : (ENNReal.ofReal s.1)⁻¹ < ∞ := ENNReal.inv_lt_top.2 hs0
  have hgapInv : (ENNReal.ofReal (s2.1 - s.1))⁻¹ < ∞ :=
    ENNReal.inv_lt_top.2 hgap0
  have hsNegNine : (ENNReal.ofReal s.1) ^ (-(9 / 2 : ℝ)) < ∞ := by
    rw [ENNReal.rpow_neg]
    exact ENNReal.inv_lt_top.2 (by positivity)
  apply ENNReal.add_lt_top.2
  constructor <;> finiteness

/-- Monotone replacement of the four local finite-`p` slots by real bounds,
with no leading order factor on the left. -/
theorem localCoarseGrainingLpRHS_le_flatComparatorSmoothLocalCoarseBound
    {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (A : Ch02.TriadicCoeffFamily d)
    (C : ℝ≥0∞) (sigma : ℝ) (hsigma : 0 < sigma)
    (g : Homogenization.Vec d → Homogenization.Vec d) (u : H1Function (openCubeSet Q))
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
          Real.rpow 3 (s2.1 * (n : ℝ)) * D := by
  let A : ℝ≥0∞ :=
    C * (ENNReal.ofReal s.1)⁻¹ * (ENNReal.ofReal sigma) ^ (1 / 2 : ℝ) *
      (ENNReal.ofReal (Real.rpow 3 s1.1) * ENNReal.ofReal E1) *
      ENNReal.ofReal S
  let B : ℝ≥0∞ :=
    C * (ENNReal.ofReal s.1) ^ (-(9 / 2 : ℝ)) *
      (ENNReal.ofReal (s2.1 - s.1))⁻¹ *
      (1 + (ENNReal.ofReal (Real.rpow 3 (s1.1 / 2)) *
        ENNReal.ofReal E2) ^ 2) *
      ENNReal.ofReal (Real.rpow 3 (s2.1 * (n : ℝ))) * ENNReal.ofReal D
  have hs0 : 0 ≤ s.1 := s.2.1.le
  have hgap0 : 0 ≤ s2.1 - s.1 := sub_nonneg.mpr hss2.le
  have hthree1 : 0 ≤ Real.rpow (3 : ℝ) s1.1 :=
    Real.rpow_nonneg (by norm_num) _
  have hthreeHalf : 0 ≤ Real.rpow (3 : ℝ) (s1.1 / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hthreeN : 0 ≤ Real.rpow (3 : ℝ) (s2.1 * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hAeq : A.toReal =
      C.toReal * s.1⁻¹ * Real.sqrt sigma * Real.rpow 3 s1.1 * E1 * S := by
    dsimp only [A]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
      ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hs0,
      ENNReal.toReal_ofReal hsigma.le, ENNReal.toReal_ofReal hE1,
      ENNReal.toReal_ofReal hS, ENNReal.toReal_ofReal hthree1]
    rw [Real.sqrt_eq_rpow]
    ring
  let T : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (s1.1 / 2)) *
    ENNReal.ofReal E2
  have hTtop : T ≠ ∞ := by
    dsimp only [T]
    finiteness
  have hTreal : T.toReal = Real.rpow 3 (s1.1 / 2) * E2 := by
    dsimp only [T]
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hthreeHalf,
      ENNReal.toReal_ofReal hE2]
  have hTpowtop : T ^ 2 ≠ ∞ := by finiteness
  have hinner : (1 + T ^ 2).toReal =
      1 + (Real.rpow 3 (s1.1 / 2) * E2) ^ 2 := by
    rw [ENNReal.toReal_add ENNReal.one_ne_top hTpowtop,
      ENNReal.toReal_one, ENNReal.toReal_pow, hTreal]
  have hBeq : B.toReal =
      C.toReal * Real.rpow s.1 (-(9 / 2 : ℝ)) *
        (s2.1 - s.1)⁻¹ *
        (1 + (Real.rpow 3 (s1.1 / 2) * E2) ^ 2) *
        Real.rpow 3 (s2.1 * (n : ℝ)) * D := by
    change (C * (ENNReal.ofReal s.1) ^ (-(9 / 2 : ℝ)) *
      (ENNReal.ofReal (s2.1 - s.1))⁻¹ * (1 + T ^ 2) *
      ENNReal.ofReal (Real.rpow 3 (s2.1 * (n : ℝ))) *
      ENNReal.ofReal D).toReal = _
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
      ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hs0,
      ENNReal.toReal_ofReal hgap0, hinner,
      ENNReal.toReal_ofReal hD, ENNReal.toReal_ofReal hthreeN]
    rw [show s.1 ^ (-(9 / 2 : ℝ)) =
      Real.rpow s.1 (-(9 / 2 : ℝ)) by rfl]
  have hadd : (A + B).toReal ≤ A.toReal + B.toReal := ENNReal.toReal_add_le
  change (A + B).toReal ≤ _
  rw [hAeq, hBeq] at hadd
  exact hadd

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
        (g : Homogenization.Vec d → Homogenization.Vec d),
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
        (g : Homogenization.Vec d → Homogenization.Vec d),
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


end

end SubdiffusiveProcess.SmoothDualComparison

