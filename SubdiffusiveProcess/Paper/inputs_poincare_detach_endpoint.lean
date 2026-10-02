import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.inputs_poincare_positive_integrable
import SubdiffusiveProcess.Paper.inputs_poincare_detach_interior
import SubdiffusiveProcess.Paper.inputs_Sf_besov_finite
import SubdiffusiveProcess.Lane4.Bridge
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-! ## Helpers for `inputs_poincare_detach_endpoint` -/

/-- The partial `3^{-s j}` sums are at most the full geometric series `(1 - 3^{-s})⁻¹`. -/
theorem aux_dsmax5_geom_sum_rpow_le (s : ℝ) (hs : 0 < s) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (-(s * (j : ℝ))) ≤
      (1 - (3 : ℝ) ^ (-s))⁻¹ := by
  have hgeom : ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (-(s * (j : ℝ))) =
      ∑ j ∈ Finset.range (N + 1), ((3 : ℝ) ^ (-s)) ^ j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-s)) j,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  rw [hgeom]
  have hx0 : 0 ≤ (3 : ℝ) ^ (-s) := Real.rpow_nonneg (by norm_num) _
  have hx1 : (3 : ℝ) ^ (-s) < 1 := by
    rw [Real.rpow_neg (by norm_num)]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) hs)
  have h := geom_sum_Ico_le_of_lt_one (x := (3 : ℝ) ^ (-s)) hx0 hx1 (m := 0) (n := N + 1)
  rw [Finset.range_eq_Ico]
  simpa using h

/-- The finite partial negative Besov norm at `q = 1` unwinds into the graded sum of the
descendant block-average sizes. -/
theorem aux_dsmax5_partial_eq_sum {d : ℕ}
    (Q : Homogenization.TriadicCube d) (s : ℝ)
    (F : SpatialCoordinates d → SpatialCoordinates d) (N : ℕ) :
    Homogenization.Book.Ch03.negativeBesovVectorPartialNormFinite Q s 1 N F =
      ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (-(s * (j : ℝ))) *
        Real.sqrt (Homogenization.Book.Ch03.negativeBesovVectorDepthAverage Q F j) := by
  simp [Homogenization.Book.Ch03.negativeBesovVectorPartialNormFinite,
    Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm, Real.rpow_one]

/-- The paper-normalized negative Besov norm as a scaled supremum of graded depth sums. -/
theorem aux_dsmax5_paperNorm_eq {d : ℕ}
    (Q : Homogenization.TriadicCube d) (s : ℝ)
    (F : SpatialCoordinates d → SpatialCoordinates d) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm Q s (.finite 1) F =
      s * sSup (Set.range fun N : ℕ => ∑ j ∈ Finset.range (N + 1),
        (3 : ℝ) ^ (-(s * (j : ℝ))) *
          Real.sqrt (Homogenization.Book.Ch03.negativeBesovVectorDepthAverage Q F j)) := by
  have h1 : ((1 : ℝ) / 1) = 1 := by norm_num
  rw [SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm,
    Homogenization.Book.Ch03.scaleNormalizedNegativeBesovVectorNorm, h1,
    show Real.rpow s 1 = s from Real.rpow_one s]
  congr 1
  apply congrArg sSup
  ext x
  constructor
  · rintro ⟨N, rfl⟩; exact ⟨N, (aux_dsmax5_partial_eq_sum Q s F N).symm⟩
  · rintro ⟨N, rfl⟩; exact ⟨N, aux_dsmax5_partial_eq_sum Q s F N⟩

/-- A descendant block-average gradient size is at most the normalized `L²` norm of the gradient
(Jensen). -/
theorem aux_dsmax5_depthAverage_le_L2Norm {d : ℕ}
    (Q : Homogenization.TriadicCube d) (F : SpatialCoordinates d → SpatialCoordinates d)
    (hF : MemLp F 2 (Homogenization.normalizedCubeMeasure Q)) (j : ℕ) :
    Real.sqrt (Homogenization.Book.Ch03.negativeBesovVectorDepthAverage Q F j) ≤
      Real.sqrt (∫ x, Homogenization.vecNormSq (F x)
        ∂Homogenization.normalizedCubeMeasure Q) := by
  rw [Homogenization.Book.Ch03.negativeBesovVectorDepthAverage]
  apply Real.sqrt_le_sqrt
  have hco : ∀ i : Fin d, MemLp (fun x => F x i) 2 (Homogenization.normalizedCubeMeasure Q) :=
    fun i => (MeasureTheory.memLp_pi_iff.mp hF) i
  have hgint : Integrable (fun x => Homogenization.vecNormSq (F x))
      (Homogenization.normalizedCubeMeasure Q) := by
    have hEq : (fun x => Homogenization.vecNormSq (F x)) =
        fun x => ∑ i : Fin d, (F x i) ^ 2 := by
      funext x; simp [Homogenization.vecNormSq, Homogenization.vecDot, pow_two]
    rw [hEq]
    exact integrable_finset_sum _ (fun i _ => (hco i).integrable_sq)
  have hpart := Homogenization.cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      Q j (fun x => Homogenization.vecNormSq (F x))
      (Homogenization.integrableOn_of_integrable_normalizedCubeMeasure Q hgint)
  rw [← Homogenization.cubeAverage_eq_integral_normalizedCubeMeasure Q
        (fun x => Homogenization.vecNormSq (F x)), hpart]
  apply Homogenization.descendantsAverage_le_descendantsAverage
  intro R hR
  have hFR : MemLp F 2 (Homogenization.normalizedCubeMeasure R) :=
    Homogenization.memLp_on_descendant_of_memLp_generic hR hF
  calc Homogenization.vecNormSq (Homogenization.cubeAverageVec R F)
      = ∑ i : Fin d, (Homogenization.cubeAverageVec R F i) ^ 2 := by
        simp [Homogenization.vecNormSq, Homogenization.vecDot, pow_two]
    _ ≤ ∑ i : Fin d, Homogenization.cubeAverage R (fun x => (F x i) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        exact Homogenization.sq_cubeAverage_le_cubeAverage_sq_of_memLp R (fun x => F x i)
          ((MeasureTheory.memLp_pi_iff.mp hFR) i)
    _ = Homogenization.cubeAverage R (fun x => Homogenization.vecNormSq (F x)) := by
        rw [Homogenization.cubeAverage_eq_integral_normalizedCubeMeasure R
              (fun x => Homogenization.vecNormSq (F x))]
        rw [show (fun x => Homogenization.vecNormSq (F x)) =
              fun x => ∑ i : Fin d, (F x i) ^ 2 by
            funext x; simp [Homogenization.vecNormSq, Homogenization.vecDot, pow_two]]
        rw [MeasureTheory.integral_finset_sum Finset.univ
          (fun i _ => ((MeasureTheory.memLp_pi_iff.mp hFR) i).integrable_sq)]
        apply Finset.sum_congr rfl
        intro i _
        rw [Homogenization.cubeAverage_eq_integral_normalizedCubeMeasure]

/-- The exponent-one graded sums of an `L²` gradient are bounded. -/
theorem aux_dsmax5_partial_one_bddAbove {d : ℕ}
    (Q : Homogenization.TriadicCube d) (F : SpatialCoordinates d → SpatialCoordinates d)
    (hF : MemLp F 2 (Homogenization.normalizedCubeMeasure Q)) :
    BddAbove (Set.range fun N : ℕ =>
      Homogenization.Book.Ch03.negativeBesovVectorPartialNormFinite Q 1 1 N F) := by
  refine ⟨Real.sqrt (∫ x, Homogenization.vecNormSq (F x)
    ∂Homogenization.normalizedCubeMeasure Q) * (3 / 2), ?_⟩
  rintro y ⟨N, rfl⟩
  have hb : Homogenization.Book.Ch03.negativeBesovVectorPartialNormFinite Q 1 1 N F ≤
      Real.sqrt (∫ x, Homogenization.vecNormSq (F x)
        ∂Homogenization.normalizedCubeMeasure Q) * (3 / 2) := by
    rw [aux_dsmax5_partial_eq_sum Q 1 F N]
    calc ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (-(1 * (j : ℝ))) *
          Real.sqrt (Homogenization.Book.Ch03.negativeBesovVectorDepthAverage Q F j)
        ≤ ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (-(1 * (j : ℝ))) *
            Real.sqrt (∫ x, Homogenization.vecNormSq (F x)
              ∂Homogenization.normalizedCubeMeasure Q) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (aux_dsmax5_depthAverage_le_L2Norm Q F hF j)
            (Real.rpow_nonneg (by norm_num) _)
      _ = Real.sqrt (∫ x, Homogenization.vecNormSq (F x)
            ∂Homogenization.normalizedCubeMeasure Q) *
            ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (-(1 * (j : ℝ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ ≤ Real.sqrt (∫ x, Homogenization.vecNormSq (F x)
            ∂Homogenization.normalizedCubeMeasure Q) * (3 / 2) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          have h := aux_dsmax5_geom_sum_rpow_le 1 (by norm_num) N
          have h32 : (1 - (3 : ℝ) ^ (-(1 : ℝ)))⁻¹ = 3 / 2 := by norm_num
          rwa [h32] at h
  exact hb

/-- The order-`0` exact-overlap depth term is at most the term of any order `t ≥ 0`: only the
depth weight grows. -/
theorem aux_dsmax5_term_zero_le_order {d : ℕ} (t : ℝ) (ht : 0 ≤ t)
    (f : SpatialCoordinates d → ℝ)
    (hu : Homogenization.ExactOverlapIntegrable (Homogenization.originCube d 0) f)
    (j : ℕ) :
    Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) 0 2 f hu j ≤
      Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) t 2 f hu j := by
  have hdepth : -((Homogenization.exactOverlapSourceDepth (Homogenization.originCube d 0) j : ℤ) : ℝ) =
      (j : ℝ) := by
    simp [Homogenization.exactOverlapSourceDepth, Homogenization.originCube]
  have hweight : Homogenization.exactOverlapDepthWeight (Homogenization.originCube d 0) 0 j ≤
      Homogenization.exactOverlapDepthWeight (Homogenization.originCube d 0) t j := by
    calc
      Homogenization.exactOverlapDepthWeight (Homogenization.originCube d 0) 0 j =
          (3 : ℝ≥0∞) ^ 0 := by
        simp [Homogenization.exactOverlapDepthWeight, hdepth]
      _ ≤ (3 : ℝ≥0∞) ^ ((j : ℝ) * t) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (mul_nonneg (Nat.cast_nonneg j) ht)
      _ = Homogenization.exactOverlapDepthWeight (Homogenization.originCube d 0) t j := by
        simp [Homogenization.exactOverlapDepthWeight, hdepth]
  rw [Homogenization.exactOverlapDepthTerm_eq, Homogenization.exactOverlapDepthTerm_eq]
  exact mul_le_mul_left hweight _

/-- The order-`0` depth supremum is at most the order-`t` supremum for `t ≥ 0`. -/
theorem aux_dsmax5_iSup_zero_le {d : ℕ} (t : ℝ) (ht : 0 ≤ t)
    (f : SpatialCoordinates d → ℝ)
    (hu : Homogenization.ExactOverlapIntegrable (Homogenization.originCube d 0) f) :
    (iSup fun j : ℕ =>
        Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) 0 2 f hu j) ≤
      (iSup fun j : ℕ =>
        Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) t 2 f hu j) :=
  iSup_le fun j =>
    (aux_dsmax5_term_zero_le_order t ht f hu j).trans
      (le_iSup (fun k : ℕ => Homogenization.exactOverlapDepthTerm
        (Homogenization.originCube d 0) t 2 f hu k) j)

/-- The order-`t` exact-overlap depth supremum of an `H¹` datum on the unit cube is finite
(as an extended nonnegative real). -/
theorem aux_dsmax5_iSup_depthTerm_lt_top {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (H : Homogenization.H1Function (Homogenization.openCubeSet (Homogenization.originCube d 0)))
    (hu : Homogenization.ExactOverlapIntegrable (Homogenization.originCube d 0) H.toFun) :
    (iSup fun j : ℕ =>
      Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) t 2 H.toFun hu j) < ⊤ := by
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d 0
  let i₀ : Fin d := ⟨0, by omega⟩
  let G : Homogenization.CubeVectorH1Function Q :=
    ⟨fun i => if i = i₀ then H else 0⟩
  have hcoordFun : (fun x => G.toField x i₀) = H.toFun := by
    funext x
    change (if i₀ = i₀ then H else 0).toFun x = H.toFun x
    simp
  have hmemVec := G.memLp_toField_normalizedCubeMeasure
  have hmem : MemLp H.toFun (2 : ℝ≥0∞) (Homogenization.normalizedCubeMeasure Q) := by
    rw [← hcoordFun]
    exact hmemVec.eval i₀
  have hscaleW : Homogenization.cubeBesovScaleWeight t Q = 1 := by
    dsimp [Q, Homogenization.cubeBesovScaleWeight]
    simp
  have hK : 0 ≤ Homogenization.cubeVectorH1OverlapPoincareConstant d *
      G.relativeGradientCoordL2NormSum :=
    mul_nonneg (Homogenization.cubeVectorH1OverlapPoincareConstant_nonneg d)
      G.relativeGradientCoordL2NormSum_nonneg
  have hdepth : ∀ j : ℕ,
      Homogenization.cubeBesovOverlapDepthSeminorm Q t (2 : ℝ≥0∞) H.toFun j ≤
        Real.rpow (3 : ℝ) ((t - 1) * (j : ℝ)) *
          (Homogenization.cubeVectorH1OverlapPoincareConstant d *
            G.relativeGradientCoordL2NormSum) := by
    intro j
    have hPoincare := Homogenization.cubeVectorH1OverlapPoincareEstimate d Q j G
    have hmul : Real.rpow (3 : ℝ) (t * (j : ℝ)) *
        Real.rpow (3 : ℝ) (-(j : ℝ)) =
        Real.rpow (3 : ℝ) ((t - 1) * (j : ℝ)) := by
      have h := Real.rpow_add (show (0 : ℝ) < 3 by norm_num)
        (t * (j : ℝ)) (-(j : ℝ))
      have he : t * (j : ℝ) + -(j : ℝ) = (t - 1) * (j : ℝ) := by ring
      rw [he] at h
      exact h.symm
    have hvector :
        Homogenization.cubeBesovOverlappingPositiveVectorDepthSeminorm Q t G.toField j ≤
          Real.rpow (3 : ℝ) ((t - 1) * (j : ℝ)) *
            (Homogenization.cubeVectorH1OverlapPoincareConstant d *
              G.relativeGradientCoordL2NormSum) := by
      unfold Homogenization.cubeBesovOverlappingPositiveVectorDepthSeminorm
      calc
        Real.rpow (3 : ℝ) (t * (j : ℝ)) *
            Real.sqrt (Homogenization.cubeBesovOverlappingPositiveVectorDepthAverage Q G.toField j)
            ≤ Real.rpow (3 : ℝ) (t * (j : ℝ)) *
                (Homogenization.cubeVectorH1OverlapPoincareConstant d *
                  Real.rpow (3 : ℝ) (-(j : ℝ)) * G.relativeGradientCoordL2NormSum) :=
          mul_le_mul_of_nonneg_left hPoincare
            (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
        _ = Real.rpow (3 : ℝ) ((t - 1) * (j : ℝ)) *
              (Homogenization.cubeVectorH1OverlapPoincareConstant d *
                G.relativeGradientCoordL2NormSum) := by
          rw [← hmul]
          ring
    calc
      Homogenization.cubeBesovOverlapDepthSeminorm Q t (2 : ℝ≥0∞) H.toFun j =
          Homogenization.cubeBesovOverlapDepthSeminorm Q t (2 : ℝ≥0∞)
            (fun x => G.toField x i₀) j := by rw [hcoordFun]
      _ ≤ Homogenization.cubeBesovScaleWeight t Q *
            Homogenization.cubeBesovOverlappingPositiveVectorDepthSeminorm
              Q t G.toField j := by
        exact Homogenization.cubeBesovOverlapDepthSeminorm_two_coordinate_le_vector
          Q t G.toField i₀ j hmemVec
      _ ≤ Homogenization.cubeBesovScaleWeight t Q *
            (Real.rpow (3 : ℝ) ((t - 1) * (j : ℝ)) *
              (Homogenization.cubeVectorH1OverlapPoincareConstant d *
                G.relativeGradientCoordL2NormSum)) :=
        mul_le_mul_of_nonneg_left hvector
          (Homogenization.cubeBesovScaleWeight_nonneg t Q)
      _ = Real.rpow (3 : ℝ) ((t - 1) * (j : ℝ)) *
            (Homogenization.cubeVectorH1OverlapPoincareConstant d *
              G.relativeGradientCoordL2NormSum) := by rw [hscaleW, one_mul]
  have hgeom : ∀ j : ℕ, Real.rpow (3 : ℝ) ((t - 1) * (j : ℝ)) ≤ 1 := by
    intro j
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [ht.2]) (Nat.cast_nonneg j)
  have hbound : ∀ j : ℕ,
      Homogenization.exactOverlapDepthTerm Q t 2 H.toFun hu j ≤
        ENNReal.ofReal (Homogenization.cubeVectorH1OverlapPoincareConstant d *
          G.relativeGradientCoordL2NormSum) := by
    intro j
    rw [aux_inputs_Sf_besov_finite_exactTerm_eq Q t H.toFun hu hmem j]
    apply ENNReal.ofReal_le_ofReal
    calc
      Homogenization.cubeBesovOverlapDepthSeminorm Q t (2 : ℝ≥0∞) H.toFun j ≤
          Real.rpow (3 : ℝ) ((t - 1) * (j : ℝ)) *
            (Homogenization.cubeVectorH1OverlapPoincareConstant d *
              G.relativeGradientCoordL2NormSum) := hdepth j
      _ ≤ 1 * (Homogenization.cubeVectorH1OverlapPoincareConstant d *
            G.relativeGradientCoordL2NormSum) :=
        mul_le_mul_of_nonneg_right (hgeom j) hK
      _ = Homogenization.cubeVectorH1OverlapPoincareConstant d *
            G.relativeGradientCoordL2NormSum := one_mul _
  have hsup : (iSup fun j : ℕ => Homogenization.exactOverlapDepthTerm Q t 2 H.toFun hu j) ≤
      ENNReal.ofReal (Homogenization.cubeVectorH1OverlapPoincareConstant d *
        G.relativeGradientCoordL2NormSum) := iSup_le hbound
  exact lt_of_le_of_lt hsup ENNReal.ofReal_lt_top

/-- **Graded-sum scale choice** (pooled leaf). -/
theorem aux_dsmax5_graded_sum_choose_scale (A : ℕ → ℝ) (M T : ℝ)
    (hA0 : ∀ j, 0 ≤ A j) (hM : ∀ j, A j ≤ M) (hM0 : 0 < M) (hT0 : 0 ≤ T)
    (hTc : ∀ N, ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (-(j : ℝ)) * A j ≤ T) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      s * sSup (Set.range fun N : ℕ => ∑ j ∈ Finset.range (N + 1),
        (3 : ℝ) ^ (-(s * (j : ℝ))) * A j) ≤ 3 * T := by
  by_cases hT : T = 0
  · subst hT
    have hA_all0 : ∀ j, A j = 0 := by
      intro j
      have hnn : ∀ k ∈ Finset.range (j+1), 0 ≤ (3:ℝ)^(-(k:ℝ))*A k :=
        fun k _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hA0 k)
      have hsum0 : ∑ k ∈ Finset.range (j+1), (3:ℝ)^(-(k:ℝ))*A k = 0 :=
        le_antisymm (hTc j) (Finset.sum_nonneg hnn)
      have hk : (3:ℝ)^(-(j:ℝ))*A j = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 j (Finset.mem_range.mpr (Nat.lt_succ_self j))
      exact (mul_eq_zero.mp hk).resolve_left (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _))
    refine ⟨1/2, by norm_num, by norm_num, ?_⟩
    have hsSup : sSup (Set.range fun N : ℕ => ∑ j ∈ Finset.range (N+1), (3:ℝ)^(-((1/2)*(j:ℝ)))*A j) = 0 := by
      have hrange : (Set.range fun N : ℕ => ∑ j ∈ Finset.range (N+1), (3:ℝ)^(-((1/2)*(j:ℝ)))*A j) = {0} := by
        ext b
        constructor
        · rintro ⟨N, rfl⟩
          simp only [Set.mem_singleton_iff]
          exact Finset.sum_eq_zero (fun j _ => by rw [hA_all0 j, mul_zero])
        · intro hb
          rw [hb]
          exact ⟨0, by simp [hA_all0]⟩
      rw [hrange, csSup_singleton]
    rw [hsSup]
    norm_num
  · have hTpos : 0 < T := lt_of_le_of_ne hT0 (Ne.symm hT)
    set c : ℝ := Real.logb 3 2 with hc_def
    have h3c : (3:ℝ)^c = 2 := by
      rw [hc_def]
      exact Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
    have hcpos : 0 < c := by
      have h : (3:ℝ)^(0:ℝ) < (3:ℝ)^c := by rw [Real.rpow_zero, h3c]; norm_num
      exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ)<3)).mp h
    have hclt1 : c < 1 := by
      have h : (3:ℝ)^c < (3:ℝ)^(1:ℝ) := by rw [h3c, Real.rpow_one]; norm_num
      exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ)<3)).mp h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max (10*M/T) 3) (show (1:ℝ) < 3 by norm_num)
    have hn3 : (3:ℝ) < (3:ℝ)^n := lt_of_le_of_lt (le_max_right _ _) hn
    have hnM : 10*M/T < (3:ℝ)^n := lt_of_le_of_lt (le_max_left _ _) hn
    have hn_ne0 : n ≠ 0 := by
      rintro rfl
      simp only [pow_zero] at hn3
      norm_num at hn3
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn_ne0
    have hnRpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn_pos
    have hnR_ge1 : (1:ℝ) ≤ (n:ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn_ne0)
    set s : ℝ := 1 - c/(n:ℝ) with hs_def
    have h1s : 1 - s = c/(n:ℝ) := by rw [hs_def]; ring
    have hcn : c/(n:ℝ) ≤ c := by
      rw [div_le_iff₀ hnRpos]
      nlinarith [hcpos.le, hnR_ge1]
    have hspos : 0 < s := by
      rw [hs_def]
      have : c/(n:ℝ) < 1 := (div_lt_one hnRpos).mpr (lt_of_lt_of_le hclt1 hnR_ge1)
      linarith
    have hslt1 : s < 1 := by
      rw [hs_def]
      have : 0 < c/(n:ℝ) := div_pos hcpos hnRpos
      linarith
    have hbase : (3:ℝ)^((1-s)*(n:ℝ)) = 2 := by
      rw [h1s, div_mul_cancel₀ c (ne_of_gt hnRpos), h3c]
    have hhead : ∀ j, j < n → (3:ℝ)^((1-s)*(j:ℝ)) ≤ 2 := by
      intro j hj
      have hle : (j:ℝ) ≤ (n:ℝ) := by exact_mod_cast (le_of_lt hj)
      have hsj : (1-s)*(j:ℝ) ≤ c := by
        rw [h1s]
        have h2 := mul_le_mul_of_nonneg_left hle (div_nonneg hcpos.le hnRpos.le)
        rwa [div_mul_cancel₀ c (ne_of_gt hnRpos)] at h2
      have h3 : (3:ℝ)^((1-s)*(j:ℝ)) ≤ (3:ℝ)^c :=
        (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ)<3)).mpr hsj
      rwa [h3c] at h3
    have hsum_le_T : ∑ j ∈ Finset.range n, (3:ℝ)^(-(j:ℝ))*A j ≤ T := by
      have hsub : Finset.range n ⊆ Finset.range (n+1) :=
        Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (Nat.lt_succ_of_lt hx))
      have hnn : ∀ j ∈ Finset.range (n+1), j ∉ Finset.range n → 0 ≤ (3:ℝ)^(-(j:ℝ))*A j :=
        fun j _ _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hA0 j)
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn).trans (hTc n)
    have hhead_sum : ∑ j ∈ Finset.range n, (3:ℝ)^(-(s*(j:ℝ)))*A j ≤ 2*T := by
      have hpt : ∀ j ∈ Finset.range n, (3:ℝ)^(-(s*(j:ℝ)))*A j ≤ 2*((3:ℝ)^(-(j:ℝ))*A j) := by
        intro j hj
        have hj_lt : j < n := Finset.mem_range.mp hj
        have heq : (3:ℝ)^(-(s*(j:ℝ))) = (3:ℝ)^((1-s)*(j:ℝ)) * (3:ℝ)^(-(j:ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
          congr 1
          ring
        rw [heq]
        have hA : 0 ≤ (3:ℝ)^(-(j:ℝ)) * A j := mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hA0 j)
        calc (3:ℝ)^((1-s)*(j:ℝ)) * (3:ℝ)^(-(j:ℝ)) * A j
            = (3:ℝ)^((1-s)*(j:ℝ)) * ((3:ℝ)^(-(j:ℝ)) * A j) := by ring
          _ ≤ 2 * ((3:ℝ)^(-(j:ℝ)) * A j) := mul_le_mul_of_nonneg_right (hhead j hj_lt) hA
      calc ∑ j ∈ Finset.range n, (3:ℝ)^(-(s*(j:ℝ)))*A j
          ≤ ∑ j ∈ Finset.range n, 2*((3:ℝ)^(-(j:ℝ))*A j) := Finset.sum_le_sum hpt
        _ = 2 * ∑ j ∈ Finset.range n, (3:ℝ)^(-(j:ℝ))*A j := by rw [Finset.mul_sum]
        _ ≤ 2 * T := mul_le_mul_of_nonneg_left hsum_le_T (by norm_num)
    have h6 : M * (6 * ((3:ℝ)^n)⁻¹) ≤ T := by
      have h3npos : (0:ℝ) < (3:ℝ)^n := pow_pos (by norm_num : (0:ℝ)<3) n
      have hkey : M * (6 * ((3:ℝ)^n)⁻¹) = 6*M/(3:ℝ)^n := by rw [div_eq_mul_inv]; ring
      rw [hkey, div_le_iff₀ h3npos]
      have hh : 10*M < (3:ℝ)^n * T := (div_lt_iff₀ hTpos).mp hnM
      nlinarith
    have htail_bound : ∀ N, ∑ j ∈ Finset.Ico n (N+1), (3:ℝ)^(-(s*(j:ℝ)))*A j ≤ T := by
      intro N
      have hSn : (3:ℝ)^(-(s*(n:ℝ))) = 2 * ((3:ℝ)^n)⁻¹ := by
        have hexp : -(s*(n:ℝ)) = -(n:ℝ) + (1-s)*(n:ℝ) := by ring
        rw [hexp, Real.rpow_add (by norm_num : (0:ℝ)<3), hbase]
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3), Real.rpow_natCast]
        ring
      have hx0 : 0 ≤ (3:ℝ)^(-s) := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _
      have hx1 : (3:ℝ)^(-s) < 1 := by
        have hh : (3:ℝ)^(-s) < (3:ℝ)^(0:ℝ) :=
          (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ)<3)).mpr (by linarith [hspos])
        rwa [Real.rpow_zero] at hh
      have hgeom : ∑ j ∈ Finset.Ico n (N+1), (3:ℝ)^(-(s*(j:ℝ))) ≤
          (3:ℝ)^(-(s*(n:ℝ)))/(1-(3:ℝ)^(-s)) := by
        have h := geom_sum_Ico_le_of_lt_one (x := (3:ℝ)^(-s)) hx0 hx1 (m := n) (n := N+1)
        have hleft : ∑ j ∈ Finset.Ico n (N+1), ((3:ℝ)^(-s))^j
            = ∑ j ∈ Finset.Ico n (N+1), (3:ℝ)^(-(s*(j:ℝ))) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Real.rpow_natCast ((3:ℝ)^(-s)) j, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
          congr 1
          ring
        have hright : ((3:ℝ)^(-s))^n = (3:ℝ)^(-(s*(n:ℝ))) := by
          rw [← Real.rpow_natCast ((3:ℝ)^(-s)) n, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
          congr 1
          ring
        rwa [hleft, hright] at h
      have hden : (1:ℝ)/3 ≤ 1 - (3:ℝ)^(-s) := by
        have hle : (3:ℝ)^(-s) ≤ (3:ℝ)^(c-1) :=
          (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ)<3)).mpr (by linarith [hs_def, hcn])
        have hval : (3:ℝ)^(c-1) = (2:ℝ)/3 := by
          rw [Real.rpow_sub (by norm_num : (0:ℝ)<3), h3c, Real.rpow_one]
        rw [hval] at hle
        linarith
      have hnum : 0 ≤ 2 * ((3:ℝ)^n)⁻¹ := by positivity
      have h1 : (3:ℝ)^(-(s*(n:ℝ)))/(1-(3:ℝ)^(-s)) ≤ 6 * ((3:ℝ)^n)⁻¹ := by
        calc (3:ℝ)^(-(s*(n:ℝ)))/(1-(3:ℝ)^(-s))
            = (2 * ((3:ℝ)^n)⁻¹)/(1-(3:ℝ)^(-s)) := by rw [hSn]
          _ ≤ (2 * ((3:ℝ)^n)⁻¹)/((1:ℝ)/3) := div_le_div_of_nonneg_left hnum (by norm_num) hden
          _ = 6 * ((3:ℝ)^n)⁻¹ := by ring
      calc ∑ j ∈ Finset.Ico n (N+1), (3:ℝ)^(-(s*(j:ℝ)))*A j
          ≤ ∑ j ∈ Finset.Ico n (N+1), M * (3:ℝ)^(-(s*(j:ℝ))) :=
            Finset.sum_le_sum (fun j _ => by
              calc (3:ℝ)^(-(s*(j:ℝ))) * A j ≤ (3:ℝ)^(-(s*(j:ℝ))) * M :=
                    mul_le_mul_of_nonneg_left (hM j) (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _)
                _ = M * (3:ℝ)^(-(s*(j:ℝ))) := by ring)
        _ = M * ∑ j ∈ Finset.Ico n (N+1), (3:ℝ)^(-(s*(j:ℝ))) := by rw [Finset.mul_sum]
        _ ≤ M * ((3:ℝ)^(-(s*(n:ℝ)))/(1-(3:ℝ)^(-s))) := mul_le_mul_of_nonneg_left hgeom hM0.le
        _ ≤ M * (6 * ((3:ℝ)^n)⁻¹) := mul_le_mul_of_nonneg_left h1 hM0.le
        _ ≤ T := h6
    have hpartial : ∀ N, ∑ j ∈ Finset.range (N+1), (3:ℝ)^(-(s*(j:ℝ)))*A j ≤ 3*T := by
      intro N
      rcases le_or_gt n (N+1) with hle | hlt
      · have hsplit := Finset.sum_range_add_sum_Ico (fun j => (3:ℝ)^(-(s*(j:ℝ)))*A j) hle
        rw [← hsplit]
        linarith [hhead_sum, htail_bound N]
      · have hsub : Finset.range (N+1) ⊆ Finset.range n :=
          Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega))
        have hnn : ∀ j ∈ Finset.range n, j ∉ Finset.range (N+1) → 0 ≤ (3:ℝ)^(-(s*(j:ℝ)))*A j :=
          fun j _ _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hA0 j)
        have h := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
        linarith [h, hhead_sum]
    refine ⟨s, hspos, hslt1, ?_⟩
    have hbdd : BddAbove (Set.range fun N : ℕ => ∑ j ∈ Finset.range (N+1), (3:ℝ)^(-(s*(j:ℝ)))*A j) :=
      ⟨3*T, by rintro _ ⟨N, rfl⟩; exact hpartial N⟩
    have hle : sSup (Set.range fun N : ℕ => ∑ j ∈ Finset.range (N+1), (3:ℝ)^(-(s*(j:ℝ)))*A j) ≤ 3*T :=
      csSup_le (Set.range_nonempty _) (fun b hb => by rcases hb with ⟨N, rfl⟩; exact hpartial N)
    have hSnn : 0 ≤ sSup (Set.range fun N : ℕ => ∑ j ∈ Finset.range (N+1), (3:ℝ)^(-(s*(j:ℝ)))*A j) :=
      le_trans (Finset.sum_nonneg (fun j _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hA0 j)))
        (le_csSup hbdd (Set.mem_range.mpr ⟨0, rfl⟩))
    calc s * sSup (Set.range fun N : ℕ => ∑ j ∈ Finset.range (N+1), (3:ℝ)^(-(s*(j:ℝ)))*A j)
        ≤ 1 * (3*T) := mul_le_mul hslt1.le hle hSnn (by norm_num)
      _ = 3*T := by ring

/-- The endpoint depth estimate follows from the interior estimate `inputs_poincare_detach_interior`
by the scale-selection limit `s ↑ 1`. -/
theorem aux_dsmax5_endpoint_of_interior (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      (∀ H : Homogenization.H1Function
          (Homogenization.openCubeSet (Homogenization.originCube d 0)),
          ∀ hu : Homogenization.ExactOverlapIntegrable
            (Homogenization.originCube d 0) H.toFun,
            (iSup fun j : ℕ =>
              Homogenization.exactOverlapDepthTerm
                (Homogenization.originCube d 0) 0 2 H.toFun hu j).toReal ≤
              C * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
                (Homogenization.originCube d 0) 1 (.finite 1) H.grad) := by
  obtain ⟨C₀, hC₀, hinterior⟩ := inputs_poincare_detach_interior d hd
  refine ⟨3 * C₀, by linarith, ?_⟩
  intro H hu
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d 0
  have hmem : MemLp H.grad 2 (Homogenization.normalizedCubeMeasure Q) := by
    rw [MeasureTheory.memLp_pi_iff]
    intro i
    exact H.grad_memL2_normalizedCubeMeasure i
  let A : ℕ → ℝ := fun j =>
    Real.sqrt (Homogenization.Book.Ch03.negativeBesovVectorDepthAverage Q H.grad j)
  have hA0 : ∀ j, 0 ≤ A j := fun j => Real.sqrt_nonneg _
  let P : ℝ := sSup (Set.range fun N : ℕ =>
    Homogenization.Book.Ch03.negativeBesovVectorPartialNormFinite Q 1 1 N H.grad)
  have hPn : 0 ≤ P := by
    refine le_trans ?_ (le_csSup (aux_dsmax5_partial_one_bddAbove Q H.grad hmem) ⟨0, rfl⟩)
    beta_reduce
    rw [show Homogenization.Book.Ch03.negativeBesovVectorPartialNormFinite Q 1 1 0 H.grad =
        ∑ j ∈ Finset.range (0 + 1), (3 : ℝ) ^ (-(1 * (j : ℝ))) *
          Real.sqrt (Homogenization.Book.Ch03.negativeBesovVectorDepthAverage Q H.grad j)
      from aux_dsmax5_partial_eq_sum Q 1 H.grad 0]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hA0 j)
  have hPT : ∀ N : ℕ, ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (-(j : ℝ)) * A j ≤ P := by
    intro N
    have hsum : (∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (-(j : ℝ)) * A j) =
        Homogenization.Book.Ch03.negativeBesovVectorPartialNormFinite Q 1 1 N H.grad := by
      rw [aux_dsmax5_partial_eq_sum Q 1 H.grad N]
      exact Finset.sum_congr rfl fun j _ => by
        show (3 : ℝ) ^ (-(j : ℝ)) * A j =
          (3 : ℝ) ^ (-(1 * (j : ℝ))) *
            Real.sqrt (Homogenization.Book.Ch03.negativeBesovVectorDepthAverage Q H.grad j)
        rw [one_mul]
    rw [hsum]
    exact le_csSup (aux_dsmax5_partial_one_bddAbove Q H.grad hmem) ⟨N, rfl⟩
  have hpaper1 : SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
      Q 1 (.finite 1) H.grad = P := by
    rw [aux_dsmax5_paperNorm_eq Q 1 H.grad, one_mul]
    exact congrArg sSup (by
      apply Set.ext
      intro x
      constructor
      · rintro ⟨N, rfl⟩; exact ⟨N, aux_dsmax5_partial_eq_sum Q 1 H.grad N⟩
      · rintro ⟨N, rfl⟩; exact ⟨N, (aux_dsmax5_partial_eq_sum Q 1 H.grad N).symm⟩)
  have hmain : (iSup fun j : ℕ =>
      Homogenization.exactOverlapDepthTerm Q 0 2 H.toFun hu j).toReal ≤ 3 * C₀ * P := by
    rcases lt_or_ge 0 P with hPpos | hPnonpos
    · -- nondegenerate: select the scale `s < 1`
      have hM0 : 0 < Real.sqrt (∫ x, Homogenization.vecNormSq (H.grad x)
          ∂Homogenization.normalizedCubeMeasure Q) := by
        by_contra hM
        have hMle : Real.sqrt (∫ x, Homogenization.vecNormSq (H.grad x)
            ∂Homogenization.normalizedCubeMeasure Q) ≤ 0 := le_of_not_gt hM
        have hAzero : ∀ j, A j = 0 := by
          intro j
          have hAM := aux_dsmax5_depthAverage_le_L2Norm Q H.grad hmem j
          exact le_antisymm (hAM.trans hMle) (Real.sqrt_nonneg _)
        have hPzero : P ≤ 0 := by
          refine csSup_le (Set.range_nonempty _) ?_
          rintro y ⟨N, rfl⟩
          beta_reduce
          rw [aux_dsmax5_partial_eq_sum Q 1 H.grad N]
          exact (Finset.sum_eq_zero fun (j : ℕ) _ => by
            show (3 : ℝ) ^ (-(1 * (j : ℝ))) *
              Real.sqrt (Homogenization.Book.Ch03.negativeBesovVectorDepthAverage Q H.grad j) = 0
            rw [show Real.sqrt (Homogenization.Book.Ch03.negativeBesovVectorDepthAverage Q H.grad j)
              = A j from rfl, hAzero j, mul_zero]).le
        linarith
      obtain ⟨s, hs0, hs1, hsc⟩ := aux_dsmax5_graded_sum_choose_scale A
        (Real.sqrt (∫ x, Homogenization.vecNormSq (H.grad x)
          ∂Homogenization.normalizedCubeMeasure Q)) P hA0
        (fun j => aux_dsmax5_depthAverage_le_L2Norm Q H.grad hmem j) hM0 hPpos.le hPT
      have hpaper : SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
          Q s (.finite 1) H.grad =
          s * sSup (Set.range fun N : ℕ => ∑ j ∈ Finset.range (N + 1),
            (3 : ℝ) ^ (-(s * (j : ℝ))) * A j) := by
        rw [aux_dsmax5_paperNorm_eq Q s H.grad]
      have hmono := aux_dsmax5_iSup_zero_le (d := d) (1 - s) (by linarith) H.toFun hu
      have hfin := aux_dsmax5_iSup_depthTerm_lt_top (d := d) hd (1 - s)
        ⟨by linarith, by linarith⟩ H hu
      have htoReal : (iSup fun j : ℕ =>
            Homogenization.exactOverlapDepthTerm Q 0 2 H.toFun hu j).toReal ≤
          (iSup fun j : ℕ =>
            Homogenization.exactOverlapDepthTerm Q (1 - s) 2 H.toFun hu j).toReal :=
        ENNReal.toReal_mono (ne_of_lt hfin) hmono
      calc (iSup fun j : ℕ =>
              Homogenization.exactOverlapDepthTerm Q 0 2 H.toFun hu j).toReal
          ≤ (iSup fun j : ℕ =>
              Homogenization.exactOverlapDepthTerm Q (1 - s) 2 H.toFun hu j).toReal := htoReal
        _ ≤ C₀ * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
              Q s (.finite 1) H.grad := hinterior s ⟨hs0, hs1⟩ H hu
        _ = C₀ * (s * sSup (Set.range fun N : ℕ => ∑ j ∈ Finset.range (N + 1),
              (3 : ℝ) ^ (-(s * (j : ℝ))) * A j)) := by rw [hpaper]
        _ ≤ C₀ * (3 * P) := mul_le_mul_of_nonneg_left hsc hC₀.le
        _ = 3 * C₀ * P := by ring
    · -- degenerate: `P = 0`
      have hP0 : P = 0 := le_antisymm hPnonpos hPn
      have hAzero : ∀ j, A j = 0 := by
        intro j
        have hsingle : (3 : ℝ) ^ (-(j : ℝ)) * A j ≤
            ∑ k ∈ Finset.range (j + 1), (3 : ℝ) ^ (-(k : ℝ)) * A k :=
          Finset.single_le_sum (f := fun k : ℕ => (3 : ℝ) ^ (-(k : ℝ)) * A k)
            (fun k _ => mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) (hA0 k))
            (Finset.mem_range.mpr (Nat.lt_succ_self j))
        have hle : (3 : ℝ) ^ (-(j : ℝ)) * A j ≤ 0 := by
          have := hPT j
          rw [hP0] at this
          linarith
        exact (mul_eq_zero.mp (le_antisymm hle
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hA0 j)))).resolve_left
          (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _))
      have hpaper_half : SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
          Q (1 / 2) (.finite 1) H.grad = 0 := by
        rw [aux_dsmax5_paperNorm_eq Q (1 / 2) H.grad]
        have hzero : ∀ N : ℕ, ∑ j ∈ Finset.range (N + 1),
            (3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) * A j = 0 := fun N =>
          Finset.sum_eq_zero fun (j : ℕ) _ => by rw [hAzero j, mul_zero]
        have hbdd : BddAbove (Set.range fun N : ℕ => ∑ j ∈ Finset.range (N + 1),
            (3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) * A j) :=
          ⟨0, by
            rintro y ⟨N, rfl⟩
            exact (hzero N).le⟩
        have hsup : sSup (Set.range fun N : ℕ => ∑ j ∈ Finset.range (N + 1),
            (3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) * A j) ≤ 0 :=
          csSup_le (Set.range_nonempty _) fun b hbmem => by
            obtain ⟨N, rfl⟩ := hbmem
            exact (hzero N).le
        have hnonneg : 0 ≤ sSup (Set.range fun N : ℕ => ∑ j ∈ Finset.range (N + 1),
            (3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) * A j) :=
          le_trans (Finset.sum_nonneg fun j _ =>
              mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hA0 j))
            (le_csSup hbdd ⟨0, rfl⟩)
        rw [le_antisymm hsup hnonneg, mul_zero]
      have hmono := aux_dsmax5_iSup_zero_le (d := d) (1 - 1 / 2) (by norm_num) H.toFun hu
      have hfin := aux_dsmax5_iSup_depthTerm_lt_top (d := d) hd (1 - 1 / 2)
        ⟨by norm_num, by norm_num⟩ H hu
      have htoReal : (iSup fun j : ℕ =>
            Homogenization.exactOverlapDepthTerm Q 0 2 H.toFun hu j).toReal ≤
          (iSup fun j : ℕ =>
            Homogenization.exactOverlapDepthTerm Q (1 - 1 / 2) 2 H.toFun hu j).toReal :=
        ENNReal.toReal_mono (ne_of_lt hfin) hmono
      have hmiddle := hinterior (1 / 2) ⟨by norm_num, by norm_num⟩ H hu
      rw [hpaper_half, mul_zero] at hmiddle
      have hzero_le : (iSup fun j : ℕ =>
            Homogenization.exactOverlapDepthTerm Q 0 2 H.toFun hu j).toReal ≤ 0 :=
        htoReal.trans hmiddle
      rw [hP0, mul_zero]
      exact hzero_le
  calc (iSup fun j : ℕ =>
        Homogenization.exactOverlapDepthTerm Q 0 2 H.toFun hu j).toReal
      ≤ 3 * C₀ * P := hmain
    _ = 3 * C₀ * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
          Q 1 (.finite 1) H.grad := by rw [hpaper1]
    _ = (3 * C₀) * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
          Q 1 (.finite 1) H.grad := by ring

theorem inputs_poincare_detach_endpoint (d : ℕ) (hd : 2 ≤ d) :
    (∃ C : ℝ, 0 < C ∧
      (∀ H : Homogenization.H1Function
          (Homogenization.openCubeSet (Homogenization.originCube d 0)),
          ∀ hu : Homogenization.ExactOverlapIntegrable
            (Homogenization.originCube d 0) H.toFun,
            (iSup fun j : ℕ =>
              Homogenization.exactOverlapDepthTerm
                (Homogenization.originCube d 0) 0 2 H.toFun hu j).toReal ≤
              C * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
                (Homogenization.originCube d 0) 1 (.finite 1) H.grad)) := by
  exact aux_dsmax5_endpoint_of_interior d hd

end Paper
