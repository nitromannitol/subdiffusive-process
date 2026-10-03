module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorCoarseError
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.LocalEllipticityControl
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.LocalAEEq

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

private theorem ofReal_centeredCubeScale_rpow_neg_local
    (m : ℤ) (t : ℝ) :
    (ENNReal.ofReal (centeredCubeScale m)) ^ (-t) =
      ENNReal.ofReal (Real.rpow 3 (-t * (m : ℝ))) := by
  rw [ENNReal.ofReal_rpow_of_pos (centeredCubeScale_pos m)]
  congr 1
  simp only [centeredCubeScale]
  rw [← Real.rpow_intCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

private theorem geometricWeight_one_succ (t : ℝ) (j : ℕ) :
    Ch02.geometricWeight t 1 j = Real.rpow 3 t *
      Ch02.geometricWeight t 1 (j + 1) := by
  simpa [Ch02.geometricWeight_eq_old] using
    (Homogenization.geometricWeight_one_shift (s := t) 1 j)

/-- Starting the `q=1` Chapter 2 response one scale below the root costs
exactly `3^t`. -/
theorem homogenizationErrorFinite_sub_one_infinity_one_le
    (Q : TriadicCube d) (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {t : ℝ} (ht : 0 < t) :
    Ch02.HomogenizationErrorFinite Q (Q.scale - 1) t .infinity 1 F a0 ≤
      Real.rpow 3 t *
        Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 1) F a0 := by
  let f : ℕ → ℝ := fun j => Ch02.geometricWeight t 1 j *
    Ch02.scaleResponseAtScale Q (Q.scale - (j : ℤ)) .infinity F a0
  have hsum : Summable f := by
    simpa only [f] using
      Ch02.summable_homogenizationErrorOnCube_infinity_one_terms Q F a0 ht
  have hf0 : ∀ j, 0 ≤ f j := by
    intro j
    exact mul_nonneg
      (by simpa [Ch02.geometricWeight_eq_old] using
        (Homogenization.geometricWeight_nonneg (s := t) (q := (1 : ℝ)) j
          (by positivity : 0 ≤ t * 1)))
      (Ch02.scaleResponseAtScale_infinity_nonneg Q (by omega) F a0)
  have htail : ∑' j : ℕ, f (j + 1) ≤ ∑' j : ℕ, f j := by
    have hsplit := hsum.sum_add_tsum_nat_add 1
    have hpref : 0 ≤ ∑ j ∈ Finset.range 1, f j :=
      Finset.sum_nonneg fun j _ => hf0 j
    linarith
  rw [Ch02.homogenizationErrorFinite_infinity_one_eq_tsum,
    Ch02.homogenizationErrorOnCube_infinity_one_eq_tsum]
  have hterm : (fun j : ℕ => Ch02.geometricWeight t 1 j *
        Ch02.scaleResponseAtScale Q
          (Q.scale - 1 - (j : ℤ)) .infinity F a0) =
      fun j => Real.rpow 3 t * f (j + 1) := by
    funext j
    rw [geometricWeight_one_succ]
    have hscale : Q.scale - 1 - (j : ℤ) = Q.scale - ((j + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hscale]
    simp only [f, mul_assoc]
  rw [hterm]
  calc
    (∑' j : ℕ, Real.rpow 3 t * f (j + 1)) =
        Real.rpow 3 t * ∑' j : ℕ, f (j + 1) := by
          exact Summable.tsum_mul_left _ ((summable_nat_add_iff 1).2 hsum)
    _ ≤ Real.rpow 3 t * ∑' j : ℕ, f j :=
      mul_le_mul_of_nonneg_left htail (Real.rpow_nonneg (by norm_num) _)

/-- The `q=2` squared response series is summable on every root cube. -/
private theorem summable_infinity_two_terms
    (Q : TriadicCube d) (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {t : ℝ} (ht : 0 < t) :
    Summable fun j : ℕ => Ch02.geometricWeight t 2 j *
      Ch02.maxDescendantNormalizedBlockResponseAtScale Q
        (Q.scale - (j : ℤ)) F a0 := by
  exact Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
    (s := t) (q := 2) (C := Ch02.normalizedBlockResponseUniformBound Q F a0)
    (by positivity)
    (fun j => Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
      (by omega) F a0)
    (fun j => Ch02.maxDescendantNormalizedBlockResponseAtScale_le_uniform Q
      (by omega) F a0)

/-- Starting the `q=2` Chapter 2 response one scale below the root costs
exactly `3^t`. -/
theorem homogenizationErrorFinite_sub_one_infinity_two_le
    (Q : TriadicCube d) (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {t : ℝ} (ht : 0 < t) :
    Ch02.HomogenizationErrorFinite Q (Q.scale - 1) t .infinity 2 F a0 ≤
      Real.rpow 3 t *
        Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) F a0 := by
  let f : ℕ → ℝ := fun j => Ch02.geometricWeight t 2 j *
    Ch02.maxDescendantNormalizedBlockResponseAtScale Q
      (Q.scale - (j : ℤ)) F a0
  have hsum : Summable f := by
    simpa only [f] using summable_infinity_two_terms Q F a0 ht
  have hf0 : ∀ j, 0 ≤ f j := by
    intro j
    exact mul_nonneg
      (by simpa [Ch02.geometricWeight_eq_old] using
        (Homogenization.geometricWeight_nonneg (s := t) (q := (2 : ℝ)) j
          (by positivity : 0 ≤ t * 2)))
      (Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q (by omega) F a0)
  have htail : ∑' j : ℕ, f (j + 1) ≤ ∑' j : ℕ, f j := by
    have hsplit := hsum.sum_add_tsum_nat_add 1
    have hpref : 0 ≤ ∑ j ∈ Finset.range 1, f j :=
      Finset.sum_nonneg fun j _ => hf0 j
    linarith
  have hsqFinite := Ch02.homogenizationErrorFinite_infinity_two_sq_eq_tsum
    Q (n := Q.scale - 1) (by omega) ht F a0
  have hsqFull := Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q ht F a0
  have hterm : (fun j : ℕ => Ch02.geometricWeight t 2 j *
        Ch02.maxDescendantNormalizedBlockResponseAtScale Q
          (Q.scale - 1 - (j : ℤ)) F a0) =
      fun j => Real.rpow 3 (2 * t) * f (j + 1) := by
    funext j
    have hw := Homogenization.geometricWeight_shift (s := t) (q := (2 : ℝ)) 1 j
    have hw' : Ch02.geometricWeight t 2 j = Real.rpow 3 (2 * t) *
        Ch02.geometricWeight t 2 (j + 1) := by
      calc
        Ch02.geometricWeight t 2 j = Real.rpow 3 (t * 2) *
            Ch02.geometricWeight t 2 (j + 1) := by
          simpa [Ch02.geometricWeight_eq_old] using hw
        _ = _ := by
          congr 2
          ring
    rw [hw']
    have hscale : Q.scale - 1 - (j : ℤ) = Q.scale - ((j + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hscale]
    simp only [f, mul_assoc]
  have hsq :
      Ch02.HomogenizationErrorFinite Q (Q.scale - 1) t .infinity 2 F a0 ^ 2 ≤
        Real.rpow 3 (2 * t) *
          Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) F a0 ^ 2 := by
    rw [hsqFinite, hsqFull, hterm]
    calc
      (∑' j : ℕ, Real.rpow 3 (2 * t) * f (j + 1)) =
          Real.rpow 3 (2 * t) * ∑' j : ℕ, f (j + 1) := by
            exact Summable.tsum_mul_left _ ((summable_nat_add_iff 1).2 hsum)
      _ ≤ Real.rpow 3 (2 * t) * ∑' j : ℕ, f j :=
        mul_le_mul_of_nonneg_left htail (Real.rpow_nonneg (by norm_num) _)
  have hfactor : Real.rpow 3 (2 * t) = (Real.rpow 3 t) ^ 2 := by
    calc
      Real.rpow 3 (2 * t) = Real.rpow 3 (t * 2) := by
        congr 1
        ring
      _ = Real.rpow (Real.rpow 3 t) 2 :=
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) t 2
      _ = (Real.rpow 3 t) ^ 2 := Real.rpow_natCast _ 2
  rw [hfactor] at hsq
  have hleft : 0 ≤ Ch02.HomogenizationErrorFinite Q (Q.scale - 1) t
      .infinity 2 F a0 := by
    unfold Ch02.HomogenizationErrorFinite
    apply Real.rpow_nonneg
    exact tsum_nonneg fun j => mul_nonneg
      (by simpa [Ch02.geometricWeight_eq_old] using
        (Homogenization.geometricWeight_nonneg (s := t) (q := (2 : ℝ)) j
          (by positivity : 0 ≤ t * 2)))
      (Real.rpow_nonneg
        (Ch02.scaleResponseAtScale_infinity_nonneg Q (by omega) F a0) 2)
  have hright : 0 ≤ Real.rpow 3 t *
      Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) F a0 :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (LambdaStabilitySupport.homogenizationErrorOnCube_infinity_two_nonneg
        Q F a0 ht)
  nlinarith only [hsq, hleft, hright]

/-- The parent-truncated `q=1` carrier in the finite-`p` endpoint is bounded
by the complete local Chapter 2 error of the source family. -/
theorem parentTruncatedErrorOne_sub_one_le_localError
    (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d)
    (sigma : ℝ) (hsigma : 0 < sigma) (t : FractionalOrder) :
    Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q (Q.scale - 1)
        (by omega) (A.coeffOn Q) sigma hsigma t ≤
      ENNReal.ofReal (Real.rpow 3 t.1) *
        ENNReal.ofReal (Ch02.HomogenizationErrorOnCube Q t.1 .infinity
          (.finite 1) A (scalarMatrix (d := d) sigma)) := by
  rw [parentTruncatedHomogenizationErrorInfinityOneScalar_eq_ofReal]
  let R := rootPointwiseCoeffFamily Q (A.coeffOn Q)
  have hlocal : Ch02.HomogenizationErrorOnCube Q t.1 .infinity (.finite 1) R
      (scalarMatrix (d := d) sigma) =
      Ch02.HomogenizationErrorOnCube Q t.1 .infinity (.finite 1) A
        (scalarMatrix (d := d) sigma) := by
    apply homogenizationErrorOnCube_eq_of_descendantAEEq
    intro k S hS
    exact rootPointwiseCoeffFamily_descendant_aeeq_family Q A
      (descendant_scale_le_of_mem_descendantsAtScale hS) hS
  have hreal := homogenizationErrorFinite_sub_one_infinity_one_le Q R
    (scalarMatrix (d := d) sigma) t.2.1
  rw [hlocal] at hreal
  have hc : 0 ≤ Real.rpow 3 t.1 := Real.rpow_nonneg (by norm_num) _
  rw [← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The parent-truncated `q=2` carrier in the finite-`p` endpoint is bounded
by the complete local Chapter 2 error of the source family. -/
theorem parentTruncatedErrorTwo_sub_one_le_localError
    (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d)
    (sigma : ℝ) (hsigma : 0 < sigma) (t : FractionalOrder) :
    Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q (Q.scale - 1)
        (by omega) (A.coeffOn Q) sigma hsigma t ≤
      ENNReal.ofReal (Real.rpow 3 t.1) *
        ENNReal.ofReal (Ch02.HomogenizationErrorOnCube Q t.1 .infinity
          (.finite 2) A (scalarMatrix (d := d) sigma)) := by
  rw [parentTruncatedHomogenizationErrorInfinityTwoScalar_eq_ofReal]
  let R := rootPointwiseCoeffFamily Q (A.coeffOn Q)
  have hlocal : Ch02.HomogenizationErrorOnCube Q t.1 .infinity (.finite 2) R
      (scalarMatrix (d := d) sigma) =
      Ch02.HomogenizationErrorOnCube Q t.1 .infinity (.finite 2) A
        (scalarMatrix (d := d) sigma) := by
    apply homogenizationErrorOnCube_eq_of_descendantAEEq
    intro k S hS
    exact rootPointwiseCoeffFamily_descendant_aeeq_family Q A
      (descendant_scale_le_of_mem_descendantsAtScale hS) hS
  have hreal := homogenizationErrorFinite_sub_one_infinity_two_le Q R
    (scalarMatrix (d := d) sigma) t.2.1
  rw [hlocal] at hreal
  have hc : 0 ≤ Real.rpow 3 t.1 := Real.rpow_nonneg (by norm_num) _
  rw [← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The finite-`p` endpoint and the scalar spectral readout, retaining its
exact Chapter 3 local right-hand side.  Downstream local-error and energy
lanes only have to bound the single displayed `ENNReal` carrier. -/
theorem exists_cubeLpNorm_sub_le_of_localCoarseGrainingLpRHS
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m n : ℤ) (hnm : n < m)
        (s1 s s2 : FractionalOrder), s1.1 < s.1 → s.1 < s2.1 →
      ∀ (a : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m)))
        (sigma : ℝ) (hsigma : 0 < sigma)
        (g : Vec d → Vec d),
        MemCubeEuclideanFullWsp (originCube d m) s2 FiniteLpExponent.two g →
      ∀ u v : H1Function (openCubeSet (originCube d m)),
        IsForcedEquation (originCube d m) a u g →
        IsScalarForcedEquation (originCube d m) sigma v g →
        HasH10Difference (originCube d m) u v →
      ∀ B : ℝ, 0 ≤ B →
        (ENNReal.ofReal s.1) ^ (-(1 / 2 : ℝ)) *
            localCoarseGrainingLpRHS C (originCube d m) n
              (by simpa [originCube] using hnm.le) a sigma hsigma g u
                s1 s s2 FiniteLpExponent.two ≤ ENNReal.ofReal B →
        cubeLpNorm (originCube d m) 2 (fun x => u.toFun x - v.toFun x) ≤
          (Section6Dirichlet.dirichletSpectralReadoutConstant s d *
            ENNReal.ofReal (centeredCubeScale m * sigma⁻¹ * B)).toReal := by
  obtain ⟨C, hCtop, hcg⟩ :=
    SubdiffusiveProcess.Providers.Section2.exists_generalCoarseGraining_paperDual_libraryRHS
      d hd FiniteLpExponent.two (by norm_num)
  refine ⟨C, hCtop, ?_⟩
  intro m n hnm s1 s s2 hs1s hss2 a sigma hsigma g hg u v hu hv huv B hB hRHS
  have hraw := hcg m n hnm s1 s s2 hs1s hss2 a sigma hsigma g hg u v hu hv huv
  have hphysical :
      ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) * ENNReal.ofReal sigma *
            paperNegativeFractionalDual (originCube d m) s
              FiniteLpExponent.two (centeredCubeGradientDifferenceL2Field m u v) +
          ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) *
            paperNegativeFractionalDual (originCube d m) s
              FiniteLpExponent.two
              (centeredCubeFluxDifferenceL2Field m a sigma u v) ≤
        ENNReal.ofReal B := by
    have htail := hraw.trans (by
      norm_num
      exact hRHS)
    simpa only [mul_add, mul_assoc] using htail
  have hphysical' :
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) * ENNReal.ofReal sigma *
            paperNegativeFractionalDual (originCube d m) s
              FiniteLpExponent.two (centeredCubeGradientDifferenceL2Field m u v) +
          (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
            paperNegativeFractionalDual (originCube d m) s
              FiniteLpExponent.two
              (centeredCubeFluxDifferenceL2Field m a sigma u v) ≤
        ENNReal.ofReal B := by
    rw [ofReal_centeredCubeScale_rpow_neg_local]
    exact hphysical
  exact cubeLpNorm_sub_le_spectral_of_physicalCoarseGraining m hsigma s u v huv
    (centeredCubeFluxDifferenceL2Field m a sigma u v) hphysical'

/-- The explicit extended-real budget obtained after replacing the two
parent-truncated response slots by the complete local Chapter 2 errors. -/
noncomputable def flatComparatorLocalCoarseBound
    (C : ℝ≥0∞) (sigma : ℝ) (s s1 s2 : FractionalOrder)
    (E1 E2 S D : ℝ) (n : ℤ) : ℝ≥0∞ :=
  (ENNReal.ofReal s.1) ^ (-(1 / 2 : ℝ)) *
    (C * (ENNReal.ofReal s.1)⁻¹ * (ENNReal.ofReal sigma) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (Real.rpow 3 s1.1) * ENNReal.ofReal E1) *
        ENNReal.ofReal S +
      C * (ENNReal.ofReal s.1) ^ (-(9 / 2 : ℝ)) *
        (ENNReal.ofReal (s2.1 - s.1))⁻¹ *
        (1 + (ENNReal.ofReal (Real.rpow 3 (s1.1 / 2)) *
          ENNReal.ofReal E2) ^ 2) *
        ENNReal.ofReal (Real.rpow 3 (s2.1 * (n : ℝ))) * ENNReal.ofReal D)

theorem flatComparatorLocalCoarseBound_lt_top
    {C : ℝ≥0∞} (hC : C < ∞) (sigma : ℝ) (s s1 s2 : FractionalOrder)
    (hss2 : s.1 < s2.1) (E1 E2 S D : ℝ) (n : ℤ) :
    flatComparatorLocalCoarseBound C sigma s s1 s2 E1 E2 S D n < ∞ := by
  unfold flatComparatorLocalCoarseBound
  have hs0 : 0 < ENNReal.ofReal s.1 := ENNReal.ofReal_pos.2 s.2.1
  have hgap0 : 0 < ENNReal.ofReal (s2.1 - s.1) :=
    ENNReal.ofReal_pos.2 (sub_pos.mpr hss2)
  have hsInv : (ENNReal.ofReal s.1)⁻¹ < ∞ := ENNReal.inv_lt_top.2 hs0
  have hgapInv : (ENNReal.ofReal (s2.1 - s.1))⁻¹ < ∞ :=
    ENNReal.inv_lt_top.2 hgap0
  have hsNegHalf : (ENNReal.ofReal s.1) ^ (-(1 / 2 : ℝ)) < ∞ := by
    rw [ENNReal.rpow_neg]
    exact ENNReal.inv_lt_top.2 (by positivity)
  have hsNegNine : (ENNReal.ofReal s.1) ^ (-(9 / 2 : ℝ)) < ∞ := by
    rw [ENNReal.rpow_neg]
    exact ENNReal.inv_lt_top.2 (by positivity)
  apply ENNReal.mul_lt_top hsNegHalf
  apply ENNReal.add_lt_top.2
  constructor <;> finiteness

/-- Monotone replacement of the four local finite-`p` slots by real bounds.
The response factors include exactly the one-level shifts proved above. -/
theorem localCoarseGrainingLpRHS_le_flatComparatorLocalCoarseBound
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
    (ENNReal.ofReal s.1) ^ (-(1 / 2 : ℝ)) *
        localCoarseGrainingLpRHS C Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) sigma hsigma g u s1 s s2 FiniteLpExponent.two ≤
      flatComparatorLocalCoarseBound C sigma s s1 s2 E1 E2 S D (Q.scale - 1) := by
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
  unfold localCoarseGrainingLpRHS flatComparatorLocalCoarseBound
  gcongr

/-- The complete local error loop: one-scale tail, finite-`p` coarse
graining, and the scalar spectral readout. -/
theorem exists_cubeLpNorm_sub_le_flatComparatorLocalCoarseBound
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (s1 s s2 : FractionalOrder), s1.1 < s.1 → s.1 < s2.1 →
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
          (Section6Dirichlet.dirichletSpectralReadoutConstant s d *
            ENNReal.ofReal (centeredCubeScale m * sigma⁻¹ *
              (flatComparatorLocalCoarseBound C sigma s s1 s2 E1 E2 S D
                (m - 1)).toReal)).toReal := by
  obtain ⟨C, hCtop, hmain⟩ :=
    exists_cubeLpNorm_sub_le_of_localCoarseGrainingLpRHS d hd
  refine ⟨C, hCtop, ?_⟩
  intro m s1 s s2 hs1s hss2 A sigma hsigma g hg u v hu hv huv
    E1 E2 S D hE1 hE2 hS hD
  let B := flatComparatorLocalCoarseBound C sigma s s1 s2 E1 E2 S D (m - 1)
  have hBtop : B < ∞ :=
    flatComparatorLocalCoarseBound_lt_top hCtop _ _ _ _ hss2 _ _ _ _ _
  have hB0 : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  apply hmain m (m - 1) (by omega) s1 s s2 hs1s hss2
    (A.coeffOn (originCube d m)) sigma hsigma g hg u v hu hv huv B.toReal hB0
  rw [ENNReal.ofReal_toReal hBtop.ne]
  exact localCoarseGrainingLpRHS_le_flatComparatorLocalCoarseBound
    (originCube d m) A C sigma hsigma g u s1 s s2 E1 E2 S D hE1 hE2
      (by simpa [originCube] using hS) hD

/-- Manuscript specialization of the flat-comparator error loop at
`(s₁,s,s₂)=(t/3,t/2,t)`.  Jensen removes the `q=1` response slot, so the only
response input is the local `(t/6,∞,2)` Chapter 2 error. -/
theorem exists_cubeLpNorm_sub_le_flatComparatorManuscriptBound
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
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
          (Section6Dirichlet.dirichletSpectralReadoutConstant smid d *
            ENNReal.ofReal (centeredCubeScale m * sigma⁻¹ *
              (flatComparatorLocalCoarseBound C sigma smid s1 s2 E E S D
                (m - 1)).toReal)).toReal := by
  obtain ⟨C, hCtop, hmain⟩ :=
    exists_cubeLpNorm_sub_le_flatComparatorLocalCoarseBound d hd
  refine ⟨C, hCtop, ?_⟩
  intro m t ht ht1 A sigma hsigma g
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
    A sigma hsigma g hg u v hu hv huv E E S D hE1
  · have heq : t / 3 / 2 = t / 6 := by ring
    simpa only [s1, heq] using hE
  · exact hS
  · exact hD

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
