module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.Carriers
public import Homogenization.Sobolev.Foundations.CubeBesovPoincare.W12Embedding
public import Homogenization.Besov.Duality.GlobalComparison
public import Homogenization.Besov.Duality.CaccioppoliBridge

@[expose] public section

/-!
# Weight bookkeeping for the multiscale Poincare route

This module records the depth weight at `(s,p,q) = (1,2,1)`, embeds the genuine
Chapter 1 mean-zero `H⁻¹` carrier into the negative-circ Besov carrier, and
defines the canonical maximizer-gradient defect used by the subsequent finite
multiscale estimates.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov

open MeasureTheory
open Homogenization Homogenization.Book
open scoped ENNReal

noncomputable section

variable {d : ℕ}

variable [NeZero d]

/-! ## The genuine mean-zero `H⁻¹` carrier -/

private theorem conjExponent_two :
    ENNReal.conjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
  simpa using
    (ENNReal.HolderConjugate.conjExponent_eq
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))

omit [NeZero d] in
private theorem meanZeroPairing_eq_cubeBesovPairing
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MemLp f (ENNReal.conjExponent (2 : ℝ≥0∞))
      (NegativeSobolev.domain (isOpenBoundedConvexDomain_openCubeSet Q)
        (Ch02.openCubeSet_nonempty Q)).normalizedVolume)
    (φ : NegativeSobolev.MeanZeroW1pTestFunction
      (isOpenBoundedConvexDomain_openCubeSet Q) (Ch02.openCubeSet_nonempty Q)
        (2 : ℝ≥0∞)) :
    NegativeSobolev.meanZeroPairing
        (isOpenBoundedConvexDomain_openCubeSet Q) (Ch02.openCubeSet_nonempty Q)
        (2 : ℝ≥0∞) (by norm_num) f hf φ =
      cubeBesovPairing Q f φ.toW1pFunction.toFun := by
  unfold NegativeSobolev.meanZeroPairing NegativeSobolev.normalizedPairing
  unfold BoundedMeasurableDomain.pairing cubeBesovPairing
  unfold BoundedMeasurableDomain.average
  rw [openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]

/-- The genuine Chapter 1 normalized mean-zero `H⁻¹` seminorm on a triadic
cube, with its `L²` witness transported across the open/half-open null boundary. -/
noncomputable def cubeMeanZeroHMinusOneSeminorm (Q : TriadicCube d)
    (f : Vec d → ℝ) (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) : ℝ≥0∞ :=
  Ch01.normalizedMeanZeroHMinusOneSeminorm (openCubeSet Q)
    (isOpenBoundedConvexDomain_openCubeSet Q) (Ch02.openCubeSet_nonempty Q) f (by
      rw [conjExponent_two,
        openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
      exact hf)

/-- The scale-free `W^{1,2} → B^1_{2,∞}` constant, made strictly positive so
that an admissible weak test can be normalized into the global Besov carrier. -/
noncomputable def cubeMeanZeroHMinusOneBesovTestConstant (d : ℕ) : ℝ :=
  cubeBesovW12EmbeddingConstant d + 1

omit [NeZero d] in
theorem cubeMeanZeroHMinusOneBesovTestConstant_pos (d : ℕ) :
    0 < cubeMeanZeroHMinusOneBesovTestConstant d := by
  unfold cubeMeanZeroHMinusOneBesovTestConstant
  exact add_pos_of_nonneg_of_pos (cubeBesovW12EmbeddingConstant_nonneg d) zero_lt_one

/-- A genuine normalized mean-zero `W^{1,2}` cube test embeds, after rescaling,
in the global `B^1_{2,∞}` test carrier.  Consequently the Chapter 1 `H⁻¹`
seminorm is controlled by the negative circ `B^{-1}_{2,1}` carrier. -/
theorem cubeMeanZeroHMinusOneSeminorm_le_cubeBesovCircNorm
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeMeanZeroHMinusOneSeminorm Q f hf ≤
      ENNReal.ofReal
        ((((3 : ℝ) ^ ((d : ℝ) + 1)) *
            cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) f) *
          cubeMeanZeroHMinusOneBesovTestConstant d) := by
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let hne := Ch02.openCubeSet_nonempty Q
  let hfOpen : MemLp f (ENNReal.conjExponent (2 : ℝ≥0∞))
      (NegativeSobolev.domain hU hne).normalizedVolume := by
    rw [conjExponent_two,
      openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    exact hf
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using conjExponent_two
  have hpConjTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [hpConj]
    norm_num
  have hqConj : cubeBesovConjExponent (1 : ℝ≥0∞) = ∞ := cubeBesovConjExponent_one
  have hCircBdd :
      BddAbove (cubeBesovCircNormValueSet Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) f) :=
    cubeBesovCircNormValueSet_bddAbove_of_memLp Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) f
      (by norm_num) hf (by norm_num) (by norm_num) (by norm_num)
  have hDualBdd :
      BddAbove (cubeBesovDualMeanZeroSeminormValueSet Q 1
        (2 : ℝ≥0∞) (1 : ℝ≥0∞) f) :=
    cubeBesovDualMeanZeroSeminormValueSet_bddAbove Q 1
      (2 : ℝ≥0∞) (1 : ℝ≥0∞) f hCircBdd hf
      (by norm_num) (by norm_num) hpConjTop (by norm_num)
  change NegativeSobolev.meanZeroNegativeSobolevSeminorm hU hne
      (2 : ℝ≥0∞) (by norm_num) (by norm_num) f hfOpen ≤ _
  rw [NegativeSobolev.meanZeroNegativeSobolevSeminorm_eq_abs]
  unfold NegativeSobolev.meanZeroNegativeSobolevAbsSeminorm
  refine iSup_le fun φ => ?_
  let g : Vec d → ℝ := φ.1.toW1pFunction.toFun
  let B : ℝ := cubeMeanZeroHMinusOneBesovTestConstant d
  have hB : 0 < B := cubeMeanZeroHMinusOneBesovTestConstant_pos d
  have hgMem : MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    rw [← openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    refine ((NegativeSobolev.domain hU hne).memLp_normalizedVolume_iff
      (2 : ℝ≥0∞) g).2 ?_
    simpa [hU, hne, g, MemLpOn, NegativeSobolev.domain,
      BoundedMeasurableDomain.restrictedVolume] using! φ.1.toW1pFunction.memLp
  have hgLocal : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g := by
    exact CubeBesovDualLocalMemLpGlobal.of_memLp_parent (p := (2 : ℝ≥0∞))
      (by simpa [hpConj] using hgMem)
  have hgSeminorm : ∀ N : ℕ,
      cubeBesovDualTestSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤
        cubeMeanZeroHMinusOneBesovTestConstant d := by
    intro N
    rw [cubeBesovDualTestSeminorm_of_conjExponent_eq_top Q 1
      (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g hqConj, hpConj]
    calc
      cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N g
          ≤ cubeBesovW12EmbeddingConstant d *
              NegativeSobolev.meanZeroTestSeminorm hU hne
                (2 : ℝ≥0∞) (by norm_num) (by norm_num) φ.1 := by
            simpa [hU, hne, g, NegativeSobolev.meanZeroTestSeminorm] using
              cubeBesovPartialSeminormTop_one_two_le_normalizedW1pSeminorm
                Q N φ.1.toW1pFunction
      _ ≤ cubeBesovW12EmbeddingConstant d * 1 := by
            exact mul_le_mul_of_nonneg_left φ.2
              (cubeBesovW12EmbeddingConstant_nonneg d)
      _ ≤ cubeMeanZeroHMinusOneBesovTestConstant d := by
            unfold cubeMeanZeroHMinusOneBesovTestConstant
            linarith
  have hgAvg : cubeAverage Q g = 0 := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure,
      ← openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    exact φ.1.normalizedIntegral_eq_zero
  let g' : Vec d → ℝ := fun x => B⁻¹ * g x
  have hg'Test : CubeBesovDualMeanZeroTestGlobal Q 1
      (2 : ℝ≥0∞) (1 : ℝ≥0∞) g' := by
    refine ⟨?_, ?_, ?_⟩
    · intro N
      calc
        cubeBesovDualTestSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g'
            = cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N g' := by
                rw [cubeBesovDualTestSeminorm_of_conjExponent_eq_top Q 1
                  (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g' hqConj, hpConj]
        _ ≤ ‖B⁻¹‖ * cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N g := by
              exact cubeBesovPartialSeminormTop_two_const_mul_le Q 1 N B⁻¹ g
        _ ≤ B⁻¹ * B := by
              have hraw := hgSeminorm N
              rw [cubeBesovDualTestSeminorm_of_conjExponent_eq_top Q 1
                (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g hqConj, hpConj] at hraw
              rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)]
              exact mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hB.le)
        _ = 1 := inv_mul_cancel₀ hB.ne'
    · dsimp [g']
      rw [cubeAverage_const_mul, hgAvg, mul_zero]
    · dsimp [g']
      exact cubeBesovDualLocalMemLpGlobal_two_const_mul B⁻¹ hgLocal
  have hpairScaled :=
    abs_cubeBesovPairing_le_cubeBesovDualMeanZeroSeminorm_of_mean_zero_test
      Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) f g' hDualBdd hg'Test
  have hdual :=
    cubeBesovDualMeanZeroSeminorm_le_note_constant_mul_cubeBesovCircNorm
      Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) f (by norm_num) hf
      (by norm_num) (by norm_num) hpConjTop (by norm_num)
  have hpair : |cubeBesovPairing Q f g| ≤
      (((3 : ℝ) ^ ((d : ℝ) + 1)) *
        cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) f) * B := by
    have hscale : |cubeBesovPairing Q f g| = B * |cubeBesovPairing Q f g'| := by
      rw [show cubeBesovPairing Q f g' = B⁻¹ * cubeBesovPairing Q f g by
        exact cubeBesovPairing_const_mul_right Q f g B⁻¹]
      rw [abs_mul, abs_of_pos (inv_pos.mpr hB)]
      field_simp [hB.ne']
    rw [hscale]
    calc
      B * |cubeBesovPairing Q f g'|
          ≤ B * cubeBesovDualMeanZeroSeminorm Q 1
              (2 : ℝ≥0∞) (1 : ℝ≥0∞) f :=
            mul_le_mul_of_nonneg_left hpairScaled hB.le
      _ ≤ B * (((3 : ℝ) ^ ((d : ℝ) + 1)) *
            cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) f) :=
          mul_le_mul_of_nonneg_left hdual hB.le
      _ = (((3 : ℝ) ^ ((d : ℝ) + 1)) *
            cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) f) * B := by ring
  refine ENNReal.ofReal_le_ofReal ?_
  rw [meanZeroPairing_eq_cubeBesovPairing Q f hfOpen φ.1]
  exact hpair

/-- Euclidean `ℓ²` aggregation of the scalar Chapter 1 mean-zero `H⁻¹`
seminorms of a vector field. -/
noncomputable def vectorCubeMeanZeroHMinusOneSeminorm (Q : TriadicCube d)
    (F : Vec d → Vec d)
    (hF : ∀ i, MemLp (fun x => F x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) : ℝ≥0∞ :=
  ENNReal.ofReal <| Real.sqrt <|
    ∑ i, (cubeMeanZeroHMinusOneSeminorm Q (fun x => F x i) (hF i)).toReal ^ 2

/-- Coordinatewise scalar duality, aggregated with the Euclidean `ℓ²` norm,
controls the vector mean-zero `H⁻¹` seminorm by the sum of the coordinate circ
norms. -/
theorem vectorCubeMeanZeroHMinusOneSeminorm_le_sum_cubeBesovCircNorm
    (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : ∀ i, MemLp (fun x => F x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    vectorCubeMeanZeroHMinusOneSeminorm Q F hF ≤
      ENNReal.ofReal
        (((3 : ℝ) ^ ((d : ℝ) + 1) * cubeMeanZeroHMinusOneBesovTestConstant d) *
          ∑ i, cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => F x i)) := by
  let A : ℝ := (3 : ℝ) ^ ((d : ℝ) + 1) * cubeMeanZeroHMinusOneBesovTestConstant d
  have hcoord_nonneg : ∀ i : Fin d,
      0 ≤ (cubeMeanZeroHMinusOneSeminorm Q (fun x => F x i) (hF i)).toReal :=
    fun _ => ENNReal.toReal_nonneg
  have hcoord : ∀ i : Fin d,
      (cubeMeanZeroHMinusOneSeminorm Q (fun x => F x i) (hF i)).toReal ≤
        A * cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => F x i) := by
    intro i
    have hi := cubeMeanZeroHMinusOneSeminorm_le_cubeBesovCircNorm Q
      (fun x => F x i) (hF i)
    have hright_ne : ENNReal.ofReal
        ((((3 : ℝ) ^ ((d : ℝ) + 1)) *
            cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => F x i)) *
          cubeMeanZeroHMinusOneBesovTestConstant d) ≠ ∞ := ENNReal.ofReal_ne_top
    have hleft_ne : cubeMeanZeroHMinusOneSeminorm Q (fun x => F x i) (hF i) ≠ ∞ :=
      ne_top_of_le_ne_top hright_ne hi
    have hitr := (ENNReal.toReal_le_toReal hleft_ne hright_ne).2 hi
    have hCircBdd : BddAbove (cubeBesovCircNormValueSet Q 1
        (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => F x i)) :=
      cubeBesovCircNormValueSet_bddAbove_of_memLp Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => F x i) (by norm_num) (hF i) (by norm_num) (by norm_num) (by norm_num)
    have hCirc : 0 ≤ cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => F x i) := cubeBesovCircNorm_nonneg Q 1 (2 : ℝ≥0∞)
          (1 : ℝ≥0∞) (fun x => F x i) hCircBdd
    have hprod : 0 ≤
        (((3 : ℝ) ^ ((d : ℝ) + 1) *
            cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => F x i)) *
          cubeMeanZeroHMinusOneBesovTestConstant d) :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hCirc)
        (cubeMeanZeroHMinusOneBesovTestConstant_pos d).le
    rw [ENNReal.toReal_ofReal hprod] at hitr
    simpa [A, mul_assoc, mul_left_comm, mul_comm] using hitr
  unfold vectorCubeMeanZeroHMinusOneSeminorm
  refine ENNReal.ofReal_le_ofReal ?_
  calc
    Real.sqrt
        (∑ i, (cubeMeanZeroHMinusOneSeminorm Q (fun x => F x i) (hF i)).toReal ^ 2)
        ≤ ∑ i, (cubeMeanZeroHMinusOneSeminorm Q (fun x => F x i) (hF i)).toReal := by
          rw [Real.sqrt_le_iff]
          constructor
          · exact Finset.sum_nonneg fun i _ => hcoord_nonneg i
          · exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hcoord_nonneg i
    _ ≤ ∑ i, A * cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => F x i) := Finset.sum_le_sum fun i _ => hcoord i
    _ = A * ∑ i, cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => F x i) := by rw [Finset.mul_sum]

/-! ## Weight bookkeeping -/

omit [NeZero d] in
/-- At `s = 1` the depth-`j` negative circ weight of a cube of scale `m` is
`3^{m-j}`.  Hence `3^{-m}` times the negative circ norm at `(s,p,q) = (1,2,1)`
is exactly the manuscript sum `Σ_{n ≤ m} 3^{-(m-n)}(avsum_z |(f)_{z+□_n}|²)^{1/2}`
under the reindexing `n = m - j`. -/
theorem cubeBesovCircDepthWeight_one (Q : TriadicCube d) (j : ℕ) :
    cubeBesovCircDepthWeight Q 1 j = (3 : ℝ) ^ Q.scale / (3 : ℝ) ^ j := by
  rw [cubeBesovCircDepthWeight, Real.rpow_one, cubeScaleFactor]

/-! ## The canonical maximizer instance -/

/-- The manuscript field `∇v(·,\cu_m,p,q;\a) - (\s_*^{-1}(\cu_m)(q+\k(\cu_m)p) -
p)`, written from the Chapter 2 canonical maximizer. -/
noncomputable def maximizerGradientDefect (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (p q : Vec d) :
    Vec d → Vec d :=
  fun x =>
    (Ch02.canonicalMaximizer
        (Ch02.responseExistenceTheory (Ch02.cubeDomain Q)
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q))
        p q).toSolution.toH1.grad x -
      coarseScaleSeparation a ha Q p q

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
