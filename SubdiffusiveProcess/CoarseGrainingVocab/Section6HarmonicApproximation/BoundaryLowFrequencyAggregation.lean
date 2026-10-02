import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryDifferencePrice
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryYoungEnvelope
import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.OneCube
import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.StandardProjectionVector
import Homogenization.Deterministic.CoarsePoincareRHS.ForceLocalization

/-!
# Finite aggregation of the boundary low-frequency terms

The support-safe boundary cutoff estimate leaves the uncentered and centered
local `L²` norms on a finite descendant partition.  This file collapses those
terms before any coefficient or scale powers are estimated.  In particular,
the uncentered squares add exactly and the centered squares cost only the
universal factor four.

PROVENANCE: this is the finite-average step following the localized
Caccioppoli estimates in
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryAssemblyEnergy.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A scalar fluctuation costs at most twice the uncentered normalized `L²`
norm on the same cube. -/
theorem cubeLpNorm_two_cubeFluctuation_le_two_mul_cubeLpNorm_two
    (Q : TriadicCube d) (u : Vec d → ℝ)
    (hu : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
      2 * cubeLpNorm Q (2 : ℝ≥0∞) u := by
  have hconst : MemLp (fun _ : Vec d ↦ -cubeAverage Q u)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_const (-cubeAverage Q u)
  have hadd : cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
      cubeLpNorm Q (2 : ℝ≥0∞) u +
        cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d ↦ -cubeAverage Q u) := by
    have hfun : cubeFluctuation Q u =
        fun x ↦ u x + (fun _ : Vec d ↦ -cubeAverage Q u) x := by
      funext x
      simp [cubeFluctuation, sub_eq_add_neg]
    rw [hfun]
    exact cubeLpNorm_add_le Q (2 : ℝ≥0∞) u
      (fun _ : Vec d ↦ -cubeAverage Q u) hu hconst (by norm_num)
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u)
        ≤ cubeLpNorm Q (2 : ℝ≥0∞) u +
            cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d ↦ -cubeAverage Q u) := hadd
    _ = cubeLpNorm Q (2 : ℝ≥0∞) u + |cubeAverage Q u| := by
      rw [cubeLpNorm_const (Q := Q) (p := (2 : ℝ≥0∞))
        (c := -cubeAverage Q u) (by norm_num)]
      simp only [Real.norm_eq_abs, abs_neg]
    _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) u +
          cubeLpNorm Q (2 : ℝ≥0∞) u := by
      gcongr
      simpa only [Real.norm_eq_abs] using norm_cubeAverage_le_cubeLpNorm_two Q u hu
    _ = 2 * cubeLpNorm Q (2 : ℝ≥0∞) u := by ring

/-- The finite descendant average of local centered scalar `L²` squares is
at most four times the parent uncentered square. -/
theorem descendantsAverage_cubeFluctuationLpNorm_two_sq_le_four_mul
    (Q : TriadicCube d) (j : ℕ) (u : Vec d → ℝ)
    (hu : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    descendantsAverage Q j (fun R ↦
        (cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuation R u)) ^ 2) ≤
      4 * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2 := by
  have hpoint : ∀ R ∈ descendantsAtDepth Q j,
      (cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuation R u)) ^ 2 ≤
        4 * (cubeLpNorm R (2 : ℝ≥0∞) u) ^ 2 := by
    intro R hR
    have huR : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp_generic hR hu
    have hle := cubeLpNorm_two_cubeFluctuation_le_two_mul_cubeLpNorm_two R u huR
    have hleft := cubeLpNorm_nonneg R (2 : ℝ≥0∞) (cubeFluctuation R u)
    have hright := cubeLpNorm_nonneg R (2 : ℝ≥0∞) u
    nlinarith only [hle, hleft, hright]
  calc
    descendantsAverage Q j (fun R ↦
        (cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuation R u)) ^ 2)
        ≤ descendantsAverage Q j (fun R ↦
            4 * (cubeLpNorm R (2 : ℝ≥0∞) u) ^ 2) :=
          descendantsAverage_le_descendantsAverage Q j hpoint
    _ = 4 * descendantsAverage Q j
          (fun R ↦ (cubeLpNorm R (2 : ℝ≥0∞) u) ^ 2) := by
      rw [descendantsAverage_mul_left]
    _ = 4 * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2 := by
      rw [show descendantsAverage Q j
          (fun R ↦ (cubeLpNorm R (2 : ℝ≥0∞) u) ^ 2) =
          cubeL2ScalarDepthAverage Q u j by rfl,
        cubeL2ScalarDepthAverage_eq_cubeLpNorm_two_sq Q u j hu]

/-- A fixed linear combination of the uncentered and centered descendant
norms has a parent square budget.  This is the precise finite low-frequency
collapse used after the explicit-height split. -/
theorem descendantsAverage_uncentered_add_fluctuation_sq_le
    (Q : TriadicCube d) (j : ℕ) (u : Vec d → ℝ) (A B : ℝ)
    (hu : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    descendantsAverage Q j (fun R ↦
        (A * cubeLpNorm R (2 : ℝ≥0∞) u +
          B * cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuation R u)) ^ 2) ≤
      (2 * A ^ 2 + 8 * B ^ 2) *
        (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2 := by
  have hpoint : ∀ R ∈ descendantsAtDepth Q j,
      (A * cubeLpNorm R (2 : ℝ≥0∞) u +
        B * cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuation R u)) ^ 2 ≤
      2 * A ^ 2 * (cubeLpNorm R (2 : ℝ≥0∞) u) ^ 2 +
        2 * B ^ 2 *
          (cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuation R u)) ^ 2 := by
    intro R _hR
    nlinarith [sq_nonneg
      (A * cubeLpNorm R (2 : ℝ≥0∞) u -
        B * cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuation R u))]
  have havg := descendantsAverage_le_descendantsAverage Q j hpoint
  rw [descendantsAverage_add_local,
    descendantsAverage_mul_left, descendantsAverage_mul_left] at havg
  have huncentered : descendantsAverage Q j
      (fun R ↦ (cubeLpNorm R (2 : ℝ≥0∞) u) ^ 2) =
      (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2 := by
    change cubeL2ScalarDepthAverage Q u j = _
    exact cubeL2ScalarDepthAverage_eq_cubeLpNorm_two_sq Q u j hu
  have hcentered :=
    descendantsAverage_cubeFluctuationLpNorm_two_sq_le_four_mul Q j u hu
  rw [huncentered] at havg
  calc
    descendantsAverage Q j (fun R ↦
        (A * cubeLpNorm R (2 : ℝ≥0∞) u +
          B * cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuation R u)) ^ 2)
        ≤ 2 * A ^ 2 * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2 +
          2 * B ^ 2 * descendantsAverage Q j (fun R ↦
            (cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuation R u)) ^ 2) := havg
    _ ≤ 2 * A ^ 2 * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2 +
          2 * B ^ 2 * (4 * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2) := by
      gcongr
    _ = (2 * A ^ 2 + 8 * B ^ 2) *
          (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2 := by ring

/-- The same finite partition preserves the squared normalized Euclidean
`L²` norm of a vector field exactly. -/
theorem descendantsAverage_boundaryNormalizedEuclideanL2_sq_eq
    (Q : TriadicCube d) (j : ℕ) (F : Vec d → Vec d)
    (hF : MemLp (fun x ↦ HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q)) :
    descendantsAverage Q j
        (fun R ↦ (boundaryNormalizedEuclideanL2 R F) ^ 2) =
      (boundaryNormalizedEuclideanL2 Q F) ^ 2 := by
  have hsquare : ∀ (R : TriadicCube d),
      MemLp (fun x ↦ HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure R) →
      (boundaryNormalizedEuclideanL2 R F) ^ 2 =
        cubeAverage R (fun x ↦ vecNormSq (F x)) := by
    intro R hFR
    have hbase := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
      (Q := R) (p := (2 : ℝ≥0∞))
      (f := fun x ↦ HilbertVec.ofVec (F x))
      (by norm_num) (by norm_num) hFR
    rw [show ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) by norm_num] at hbase
    simp only [Real.rpow_natCast] at hbase
    rw [boundaryNormalizedEuclideanL2, hbase]
    refine congrArg (cubeAverage R) ?_
    funext x
    rw [HilbertVec.norm_sq_ofVec]
    rfl
  have hint : IntegrableOn (fun x ↦ vecNormSq (F x)) (cubeSet Q) volume := by
    have hnorm : IntegrableOn
        (fun x ↦ ‖HilbertVec.ofVec (F x)‖ ^ (2 : ℝ))
        (cubeSet Q) volume :=
      integrableOn_of_integrable_normalizedCubeMeasure (Q := Q)
        (hF.integrable_norm_rpow (by norm_num) (by norm_num))
    refine hnorm.congr ?_
    filter_upwards with x
    rw [Real.rpow_two, vecNormSq]
    exact HilbertVec.norm_sq_ofVec (F x)
  calc
    descendantsAverage Q j
        (fun R ↦ (boundaryNormalizedEuclideanL2 R F) ^ 2) =
        descendantsAverage Q j
          (fun R ↦ cubeAverage R (fun x ↦ vecNormSq (F x))) := by
      change ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          (∑ R ∈ descendantsAtDepth Q j,
            (boundaryNormalizedEuclideanL2 R F) ^ 2) =
        ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          (∑ R ∈ descendantsAtDepth Q j,
            cubeAverage R (fun x ↦ vecNormSq (F x)))
      congr 1
      apply Finset.sum_congr rfl
      intro R hR
      exact hsquare R (memLp_on_descendant_of_memLp_generic hR hF)
    _ = cubeAverage Q (fun x ↦ vecNormSq (F x)) :=
      (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
        Q j (fun x ↦ vecNormSq (F x)) hint).symm
    _ = (boundaryNormalizedEuclideanL2 Q F) ^ 2 := (hsquare Q hF).symm

/-- The two source quantities left by the support-safe corrected-flux bound
have a parent-square budget: the positive Besov seminorm localizes in square
average, while the normalized Euclidean `L²` term is exactly additive. -/
theorem descendantsAverage_forceLowFrequency_sq_le
    (Q : TriadicCube d) (j : ℕ) (s A B : ℝ) (F : Vec d → Vec d)
    (hs : 0 ≤ s) (hreg : ForceBesovRegularity Q s F)
    (hHilbert : MemLp (fun x ↦ HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q)) :
    descendantsAverage Q j (fun R ↦
        (A * scaleNormalizedPositiveBesovVectorSeminormTwo R s F +
          B * boundaryNormalizedEuclideanL2 R F) ^ 2) ≤
      2 * A ^ 2 *
          (scaleNormalizedPositiveBesovVectorSeminormTwo Q s F) ^ 2 +
        2 * B ^ 2 * (boundaryNormalizedEuclideanL2 Q F) ^ 2 := by
  have hpoint : ∀ R ∈ descendantsAtDepth Q j,
      (A * scaleNormalizedPositiveBesovVectorSeminormTwo R s F +
          B * boundaryNormalizedEuclideanL2 R F) ^ 2 ≤
        2 * A ^ 2 *
            (scaleNormalizedPositiveBesovVectorSeminormTwo R s F) ^ 2 +
          2 * B ^ 2 * (boundaryNormalizedEuclideanL2 R F) ^ 2 := by
    intro R _hR
    nlinarith [sq_nonneg
      (A * scaleNormalizedPositiveBesovVectorSeminormTwo R s F -
        B * boundaryNormalizedEuclideanL2 R F)]
  have havg := descendantsAverage_le_descendantsAverage Q j hpoint
  rw [descendantsAverage_add_local,
    descendantsAverage_mul_left, descendantsAverage_mul_left] at havg
  have hlocalBdd : ∀ R ∈ descendantsAtDepth Q j,
      BddAbove (Set.range fun N : ℕ ↦
        cubeBesovPositiveVectorPartialSeminormTwo R s N F) := by
    intro R hR
    exact cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_parent_bddAbove
      s F hR hreg.partialSeminorms_bddAbove
  have hsemi :=
    descendantsAverage_sq_cubeBesovPositiveVectorSeminormTwo_le_parent_of_bddAbove
      Q F j hs hreg.partialSeminorms_bddAbove hlocalBdd
  have hL2 := descendantsAverage_boundaryNormalizedEuclideanL2_sq_eq
    Q j F hHilbert
  calc
    descendantsAverage Q j (fun R ↦
        (A * scaleNormalizedPositiveBesovVectorSeminormTwo R s F +
          B * boundaryNormalizedEuclideanL2 R F) ^ 2)
        ≤ 2 * A ^ 2 * descendantsAverage Q j (fun R ↦
            (scaleNormalizedPositiveBesovVectorSeminormTwo R s F) ^ 2) +
          2 * B ^ 2 * descendantsAverage Q j
            (fun R ↦ (boundaryNormalizedEuclideanL2 R F) ^ 2) := havg
    _ ≤ 2 * A ^ 2 *
          (scaleNormalizedPositiveBesovVectorSeminormTwo Q s F) ^ 2 +
        2 * B ^ 2 * (boundaryNormalizedEuclideanL2 Q F) ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hsemi
          (mul_nonneg (by norm_num) (sq_nonneg A)))
        (by rw [hL2])

/-- Finite aggregation of the exact Young remainder produced by
`halfAbsorb_of_twoEnergy_product_budget`.  The statement deliberately keeps
the three parent square budgets abstract; the preceding lemmas instantiate
them by the parent solution/datum and forcing norms. -/
theorem descendantsAverage_twoEnergyYoungRemainder_le
    (Q : TriadicCube d) (j : ℕ)
    (C A mu kr kg BX BY BE : ℝ)
    (X Y Eh G R : TriadicCube d → ℝ)
    (hC : 0 ≤ C) (hkr : 0 ≤ kr) (hkg : 0 ≤ kg)
    (hX : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ X S)
    (hY : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ Y S)
    (hEh : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ Eh S)
    (hG : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ G S)
    (hR0 : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ R S)
    (hR : ∀ S ∈ descendantsAtDepth Q j, R S ≤ kr * X S)
    (hGle : ∀ S ∈ descendantsAtDepth Q j, G S ≤ kg * Y S)
    (hXavg : descendantsAverage Q j (fun S ↦ (X S) ^ 2) ≤ BX)
    (hYavg : descendantsAverage Q j (fun S ↦ (Y S) ^ 2) ≤ BY)
    (hEhavg : descendantsAverage Q j Eh ≤ BE) :
    let Kz := 4 * (C * A) ^ 2 + C / 2
    let Kg := 4 * (C * (Real.sqrt 2 * mu)) ^ 2 + C / 2
    descendantsAverage Q j (fun S ↦
        let Z := Real.sqrt 2 * mu * Real.sqrt (Eh S) + R S
        4 * (C * A * Z) ^ 2 +
          4 * (C * G S * (Real.sqrt 2 * mu)) ^ 2 + C * G S * Z) ≤
      Kz * (4 * mu ^ 2 * BE + 2 * kr ^ 2 * BX) +
        Kg * (kg ^ 2 * BY) := by
  dsimp only
  let Kz : ℝ := 4 * (C * A) ^ 2 + C / 2
  let Kg : ℝ := 4 * (C * (Real.sqrt 2 * mu)) ^ 2 + C / 2
  have hKz : 0 ≤ Kz := by dsimp [Kz]; positivity
  have hKg : 0 ≤ Kg := by dsimp [Kg]; positivity
  have hpoint : ∀ S ∈ descendantsAtDepth Q j,
      (let Z := Real.sqrt 2 * mu * Real.sqrt (Eh S) + R S
       4 * (C * A * Z) ^ 2 +
          4 * (C * G S * (Real.sqrt 2 * mu)) ^ 2 + C * G S * Z) ≤
        Kz * (4 * mu ^ 2 * Eh S + 2 * kr ^ 2 * (X S) ^ 2) +
          Kg * (kg ^ 2 * (Y S) ^ 2) := by
    intro S hS
    let Z : ℝ := Real.sqrt 2 * mu * Real.sqrt (Eh S) + R S
    have hsqrtEh : (Real.sqrt (Eh S)) ^ 2 = Eh S := Real.sq_sqrt (hEh S hS)
    have hsqrt2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hRle := hR S hS
    have hGlocal := hGle S hS
    have hkrX0 : 0 ≤ kr * X S := mul_nonneg hkr (hX S hS)
    have hkgY0 : 0 ≤ kg * Y S := mul_nonneg hkg (hY S hS)
    have hZsq : Z ^ 2 ≤
        4 * mu ^ 2 * Eh S + 2 * kr ^ 2 * (X S) ^ 2 := by
      have hsumSq : Z ^ 2 ≤
          2 * (Real.sqrt 2 * mu * Real.sqrt (Eh S)) ^ 2 +
            2 * (R S) ^ 2 := by
        dsimp [Z]
        nlinarith [sq_nonneg
          (Real.sqrt 2 * mu * Real.sqrt (Eh S) - R S)]
      have hRsq : (R S) ^ 2 ≤ (kr * X S) ^ 2 := by
        nlinarith only [hRle, hR0 S hS, hkrX0]
      calc
        Z ^ 2 ≤ 2 * (Real.sqrt 2 * mu * Real.sqrt (Eh S)) ^ 2 +
            2 * (R S) ^ 2 := hsumSq
        _ ≤ 2 * (Real.sqrt 2 * mu * Real.sqrt (Eh S)) ^ 2 +
            2 * (kr * X S) ^ 2 := by nlinarith only [hRsq]
        _ = 4 * mu ^ 2 * Eh S + 2 * kr ^ 2 * (X S) ^ 2 := by
          rw [show (Real.sqrt 2 * mu * Real.sqrt (Eh S)) ^ 2 =
            (Real.sqrt 2) ^ 2 * mu ^ 2 * (Real.sqrt (Eh S)) ^ 2 by ring,
            hsqrt2, hsqrtEh]
          ring
    have hGsq : (G S) ^ 2 ≤ kg ^ 2 * (Y S) ^ 2 := by
      nlinarith only [hGlocal, hG S hS, hkgY0]
    have hcross : C * G S * Z ≤ C / 2 * ((G S) ^ 2 + Z ^ 2) := by
      have hsq := sq_nonneg (G S - Z)
      nlinarith only [hsq, hC]
    have hraw :
        4 * (C * A * Z) ^ 2 +
            4 * (C * G S * (Real.sqrt 2 * mu)) ^ 2 + C * G S * Z ≤
          Kz * Z ^ 2 + Kg * (G S) ^ 2 := by
      dsimp [Kz, Kg]
      nlinarith only [hcross]
    calc
      (let Z := Real.sqrt 2 * mu * Real.sqrt (Eh S) + R S
       4 * (C * A * Z) ^ 2 +
          4 * (C * G S * (Real.sqrt 2 * mu)) ^ 2 + C * G S * Z)
          ≤ Kz * Z ^ 2 + Kg * (G S) ^ 2 := hraw
      _ ≤ Kz * (4 * mu ^ 2 * Eh S + 2 * kr ^ 2 * (X S) ^ 2) +
          Kg * (kg ^ 2 * (Y S) ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hZsq hKz)
          (mul_le_mul_of_nonneg_left hGsq hKg)
  have havg := descendantsAverage_le_descendantsAverage Q j hpoint
  have hsplit : descendantsAverage Q j (fun S ↦
      Kz * (4 * mu ^ 2 * Eh S + 2 * kr ^ 2 * (X S) ^ 2) +
        Kg * (kg ^ 2 * (Y S) ^ 2)) =
      Kz * (4 * mu ^ 2 * descendantsAverage Q j Eh +
        2 * kr ^ 2 * descendantsAverage Q j (fun S ↦ (X S) ^ 2)) +
      Kg * (kg ^ 2 * descendantsAverage Q j (fun S ↦ (Y S) ^ 2)) := by
    rw [descendantsAverage_add_local, descendantsAverage_mul_left,
      descendantsAverage_mul_left, descendantsAverage_add_local,
      descendantsAverage_mul_left, descendantsAverage_mul_left,
      descendantsAverage_mul_left]
  rw [hsplit] at havg
  refine havg.trans ?_
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (add_le_add
        (mul_le_mul_of_nonneg_left hEhavg
          (mul_nonneg (by norm_num) (sq_nonneg mu)))
        (mul_le_mul_of_nonneg_left hXavg
          (mul_nonneg (by norm_num) (sq_nonneg kr)))) hKz)
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hYavg (sq_nonneg kg)) hKg)

/-- Normalizer-preserving finite aggregation.  Compared with
`descendantsAverage_twoEnergyYoungRemainder_le`, the cross-term Young weight
is explicit: `tau` stays on the solution/datum budget and `tau⁻¹` is charged
to the forcing budget. -/
theorem descendantsAverage_twoEnergyYoungRemainder_le_weighted
    (Q : TriadicCube d) (j : ℕ)
    (C A mu tau kr kg BX BY BE : ℝ)
    (X Y Eh G R : TriadicCube d → ℝ)
    (htau : 0 < tau) (hmu : 0 ≤ mu) (hkr : 0 ≤ kr) (hkg : 0 ≤ kg)
    (hX : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ X S)
    (hY : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ Y S)
    (hEh : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ Eh S)
    (hG : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ G S)
    (hR0 : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ R S)
    (hR : ∀ S ∈ descendantsAtDepth Q j, R S ≤ kr * X S)
    (hGle : ∀ S ∈ descendantsAtDepth Q j, G S ≤ kg * Y S)
    (hXavg : descendantsAverage Q j (fun S ↦ (X S) ^ 2) ≤ BX)
    (hYavg : descendantsAverage Q j (fun S ↦ (Y S) ^ 2) ≤ BY)
    (hEhavg : descendantsAverage Q j Eh ≤ BE) :
    let Kz := 4 * (C * A) ^ 2 + tau / 2
    let Kg := 4 * (C * Real.sqrt 2 * mu) ^ 2 + C ^ 2 / (2 * tau)
    descendantsAverage Q j (fun S ↦
        let Z := Real.sqrt 2 * mu * Real.sqrt (Eh S) + R S
        4 * (C * A * Z) ^ 2 +
          4 * (C * G S * (Real.sqrt 2 * mu)) ^ 2 + C * G S * Z) ≤
      Kz * (4 * mu ^ 2 * BE + 2 * kr ^ 2 * BX) +
        Kg * (kg ^ 2 * BY) := by
  dsimp only
  let Kz : ℝ := 4 * (C * A) ^ 2 + tau / 2
  let Kg : ℝ := 4 * (C * Real.sqrt 2 * mu) ^ 2 + C ^ 2 / (2 * tau)
  have hKz : 0 ≤ Kz := by dsimp [Kz]; positivity
  have hKg : 0 ≤ Kg := by dsimp [Kg]; positivity
  have hpoint : ∀ S ∈ descendantsAtDepth Q j,
      (let Z := Real.sqrt 2 * mu * Real.sqrt (Eh S) + R S
       4 * (C * A * Z) ^ 2 +
          4 * (C * G S * (Real.sqrt 2 * mu)) ^ 2 + C * G S * Z) ≤
        Kz * (4 * mu ^ 2 * Eh S + 2 * kr ^ 2 * (X S) ^ 2) +
          Kg * (kg ^ 2 * (Y S) ^ 2) := by
    intro S hS
    have hbase := boundaryYoungRemainder_le_weighted
      (C := C) (A := A) (mu := mu) (Eh := Eh S) (R := R S)
        (G := G S) (tau := tau) (hEh S hS) (hR0 S hS) hmu htau
    have hRle := hR S hS
    have hGlocal := hGle S hS
    have hkrX0 : 0 ≤ kr * X S := mul_nonneg hkr (hX S hS)
    have hkgY0 : 0 ≤ kg * Y S := mul_nonneg hkg (hY S hS)
    have hRsq : (R S) ^ 2 ≤ (kr * X S) ^ 2 := by
      nlinarith only [hRle, hR0 S hS, hkrX0]
    have hGsq : (G S) ^ 2 ≤ (kg * Y S) ^ 2 := by
      nlinarith only [hGlocal, hG S hS, hkgY0]
    have hinside : 4 * mu ^ 2 * Eh S + 2 * (R S) ^ 2 ≤
        4 * mu ^ 2 * Eh S + 2 * (kr * X S) ^ 2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hRsq (by norm_num))
    have hbudget := add_le_add
      (mul_le_mul_of_nonneg_left hinside hKz)
      (mul_le_mul_of_nonneg_left hGsq hKg)
    exact hbase.trans (by
      dsimp only [Kz, Kg] at hbudget ⊢
      nlinarith only [hbudget])
  have havg := descendantsAverage_le_descendantsAverage Q j hpoint
  have hsplit : descendantsAverage Q j (fun S ↦
      Kz * (4 * mu ^ 2 * Eh S + 2 * kr ^ 2 * (X S) ^ 2) +
        Kg * (kg ^ 2 * (Y S) ^ 2)) =
      Kz * (4 * mu ^ 2 * descendantsAverage Q j Eh +
        2 * kr ^ 2 * descendantsAverage Q j (fun S ↦ (X S) ^ 2)) +
      Kg * (kg ^ 2 * descendantsAverage Q j (fun S ↦ (Y S) ^ 2)) := by
    rw [descendantsAverage_add_local, descendantsAverage_mul_left,
      descendantsAverage_mul_left, descendantsAverage_add_local,
      descendantsAverage_mul_left, descendantsAverage_mul_left,
      descendantsAverage_mul_left]
  rw [hsplit] at havg
  refine havg.trans ?_
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (add_le_add
        (mul_le_mul_of_nonneg_left hEhavg
          (mul_nonneg (by norm_num) (sq_nonneg mu)))
        (mul_le_mul_of_nonneg_left hXavg
          (mul_nonneg (by norm_num) (sq_nonneg kr)))) hKz)
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hYavg (sq_nonneg kg)) hKg)

/-- The finite-cell remainder after substituting its literal solution,
forcing, and datum carriers.  Thus no local normalized norm survives this
step: only the three parent budgets remain.  The scalar coefficients are
kept explicit for the subsequent height/gap estimate. -/
theorem descendantsAverage_boundaryLowFrequencyRemainder_le_parentBudgets
    (Q : TriadicCube d) (j : ℕ) (s C A mu : ℝ)
    (Au Bu Af Bf BE : ℝ)
    (u : Vec d → ℝ) (F : Vec d → Vec d)
    (Eh : TriadicCube d → ℝ)
    (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hAu : 0 ≤ Au) (hBu : 0 ≤ Bu)
    (hAf : 0 ≤ Af) (hBf : 0 ≤ Bf)
    (hu : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hFreg : ForceBesovRegularity Q s F)
    (hFL2 : MemLp (fun x ↦ HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q))
    (hEh : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ Eh S)
    (hEhavg : descendantsAverage Q j Eh ≤ BE) :
    let Kz := 4 * (C * A) ^ 2 + C / 2
    let Kg := 4 * (C * (Real.sqrt 2 * mu)) ^ 2 + C / 2
    descendantsAverage Q j (fun S ↦
        let X := Au * cubeLpNorm S (2 : ℝ≥0∞) u +
          Bu * cubeLpNorm S (2 : ℝ≥0∞) (cubeFluctuation S u)
        let G := Af * scaleNormalizedPositiveBesovVectorSeminormTwo S s F +
          Bf * boundaryNormalizedEuclideanL2 S F
        let Z := Real.sqrt 2 * mu * Real.sqrt (Eh S) + X
        4 * (C * A * Z) ^ 2 +
          4 * (C * G * (Real.sqrt 2 * mu)) ^ 2 + C * G * Z) ≤
      Kz * (4 * mu ^ 2 * BE +
        2 * (2 * Au ^ 2 + 8 * Bu ^ 2) *
          (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2) +
      Kg * (2 * Af ^ 2 *
          (scaleNormalizedPositiveBesovVectorSeminormTwo Q s F) ^ 2 +
        2 * Bf ^ 2 * (boundaryNormalizedEuclideanL2 Q F) ^ 2) := by
  dsimp only
  let X : TriadicCube d → ℝ := fun S ↦
    Au * cubeLpNorm S (2 : ℝ≥0∞) u +
      Bu * cubeLpNorm S (2 : ℝ≥0∞) (cubeFluctuation S u)
  let G : TriadicCube d → ℝ := fun S ↦
    Af * scaleNormalizedPositiveBesovVectorSeminormTwo S s F +
      Bf * boundaryNormalizedEuclideanL2 S F
  have hX : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ X S := by
    intro S _hS
    exact add_nonneg
      (mul_nonneg hAu (cubeLpNorm_nonneg S 2 u))
      (mul_nonneg hBu (cubeLpNorm_nonneg S 2 (cubeFluctuation S u)))
  have hG : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ G S := by
    intro S hS
    have hFregS : ForceBesovRegularity S s F :=
      forceBesovRegularity_descendant hFreg hS
    exact add_nonneg
      (mul_nonneg hAf
        (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
          hFregS))
      (mul_nonneg hBf (boundaryNormalizedEuclideanL2_nonneg S F))
  have hXavg : descendantsAverage Q j (fun S ↦ (X S) ^ 2) ≤
      (2 * Au ^ 2 + 8 * Bu ^ 2) *
        (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2 := by
    simpa only [X] using
      descendantsAverage_uncentered_add_fluctuation_sq_le Q j u Au Bu hu
  have hGavg : descendantsAverage Q j (fun S ↦ (G S) ^ 2) ≤
      2 * Af ^ 2 *
          (scaleNormalizedPositiveBesovVectorSeminormTwo Q s F) ^ 2 +
        2 * Bf ^ 2 * (boundaryNormalizedEuclideanL2 Q F) ^ 2 := by
    simpa only [G] using descendantsAverage_forceLowFrequency_sq_le
      Q j s Af Bf F hs hFreg hFL2
  have hmain := descendantsAverage_twoEnergyYoungRemainder_le
      Q j C A mu 1 1
      ((2 * Au ^ 2 + 8 * Bu ^ 2) *
        (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2) (2 * Af ^ 2 *
        (scaleNormalizedPositiveBesovVectorSeminormTwo Q s F) ^ 2 +
          2 * Bf ^ 2 * (boundaryNormalizedEuclideanL2 Q F) ^ 2) BE
      X G Eh G X hC (by norm_num) (by norm_num)
      hX hG hEh hG hX
      (fun S _hS ↦ by simp) (fun S _hS ↦ by simp)
      hXavg hGavg hEhavg
  dsimp only [X, G] at hmain ⊢
  convert hmain using 1
  all_goals ring

/-- The preceding concrete finite-cell aggregation with the scalar
normalizer retained in the Young step. -/
theorem descendantsAverage_boundaryLowFrequencyRemainder_le_parentBudgets_weighted
    (Q : TriadicCube d) (j : ℕ) (s C A mu tau : ℝ)
    (Au Bu Af Bf BE : ℝ)
    (u : Vec d → ℝ) (F : Vec d → Vec d)
    (Eh : TriadicCube d → ℝ)
    (hs : 0 ≤ s) (htau : 0 < tau) (hmu : 0 ≤ mu)
    (hAu : 0 ≤ Au) (hBu : 0 ≤ Bu)
    (hAf : 0 ≤ Af) (hBf : 0 ≤ Bf)
    (hu : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hFreg : ForceBesovRegularity Q s F)
    (hFL2 : MemLp (fun x ↦ HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q))
    (hEh : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ Eh S)
    (hEhavg : descendantsAverage Q j Eh ≤ BE) :
    let Kz := 4 * (C * A) ^ 2 + tau / 2
    let Kg := 4 * (C * Real.sqrt 2 * mu) ^ 2 + C ^ 2 / (2 * tau)
    descendantsAverage Q j (fun S ↦
        let X := Au * cubeLpNorm S (2 : ℝ≥0∞) u +
          Bu * cubeLpNorm S (2 : ℝ≥0∞) (cubeFluctuation S u)
        let G := Af * scaleNormalizedPositiveBesovVectorSeminormTwo S s F +
          Bf * boundaryNormalizedEuclideanL2 S F
        let Z := Real.sqrt 2 * mu * Real.sqrt (Eh S) + X
        4 * (C * A * Z) ^ 2 +
          4 * (C * G * (Real.sqrt 2 * mu)) ^ 2 + C * G * Z) ≤
      Kz * (4 * mu ^ 2 * BE +
        2 * (2 * Au ^ 2 + 8 * Bu ^ 2) *
          (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2) +
      Kg * (2 * Af ^ 2 *
          (scaleNormalizedPositiveBesovVectorSeminormTwo Q s F) ^ 2 +
        2 * Bf ^ 2 * (boundaryNormalizedEuclideanL2 Q F) ^ 2) := by
  dsimp only
  let X : TriadicCube d → ℝ := fun S ↦
    Au * cubeLpNorm S (2 : ℝ≥0∞) u +
      Bu * cubeLpNorm S (2 : ℝ≥0∞) (cubeFluctuation S u)
  let G : TriadicCube d → ℝ := fun S ↦
    Af * scaleNormalizedPositiveBesovVectorSeminormTwo S s F +
      Bf * boundaryNormalizedEuclideanL2 S F
  have hX : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ X S := by
    intro S _hS
    exact add_nonneg
      (mul_nonneg hAu (cubeLpNorm_nonneg S 2 u))
      (mul_nonneg hBu (cubeLpNorm_nonneg S 2 (cubeFluctuation S u)))
  have hG : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ G S := by
    intro S hS
    have hFregS : ForceBesovRegularity S s F :=
      forceBesovRegularity_descendant hFreg hS
    exact add_nonneg
      (mul_nonneg hAf
        (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
          hFregS))
      (mul_nonneg hBf (boundaryNormalizedEuclideanL2_nonneg S F))
  have hXavg : descendantsAverage Q j (fun S ↦ (X S) ^ 2) ≤
      (2 * Au ^ 2 + 8 * Bu ^ 2) *
        (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2 := by
    simpa only [X] using
      descendantsAverage_uncentered_add_fluctuation_sq_le Q j u Au Bu hu
  have hGavg : descendantsAverage Q j (fun S ↦ (G S) ^ 2) ≤
      2 * Af ^ 2 *
          (scaleNormalizedPositiveBesovVectorSeminormTwo Q s F) ^ 2 +
        2 * Bf ^ 2 * (boundaryNormalizedEuclideanL2 Q F) ^ 2 := by
    simpa only [G] using descendantsAverage_forceLowFrequency_sq_le
      Q j s Af Bf F hs hFreg hFL2
  have hmain := descendantsAverage_twoEnergyYoungRemainder_le_weighted
      Q j C A mu tau 1 1
      ((2 * Au ^ 2 + 8 * Bu ^ 2) *
        (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2) (2 * Af ^ 2 *
        (scaleNormalizedPositiveBesovVectorSeminormTwo Q s F) ^ 2 +
          2 * Bf ^ 2 * (boundaryNormalizedEuclideanL2 Q F) ^ 2) BE
      X G Eh G X htau hmu (by norm_num) (by norm_num)
      hX hG hEh hG hX
      (fun S _hS ↦ by simp) (fun S _hS ↦ by simp)
      hXavg hGavg hEhavg
  dsimp only [X, G] at hmain ⊢
  convert hmain using 1
  all_goals ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
