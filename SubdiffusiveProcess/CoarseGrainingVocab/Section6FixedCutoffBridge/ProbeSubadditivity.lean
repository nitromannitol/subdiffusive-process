module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.FiniteProbeReduction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.DualAnnealedMonotone

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Re-establishing the primal subadditivity publicly -/

theorem matLoewnerLE_randomAMatrix_descendantsAverage'
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (Q : TriadicCube d)
    (j : ℕ) :
    MatLoewnerLE (randomAMatrix M L (Ch02.cubeDomain Q) omega)
      (Homogenization.descendantsAverageMat Q j fun R =>
        randomAMatrix M L (Ch02.cubeDomain R) omega) := by
  let F := aCutoffFamily M L omega
  let Pcell : Ch02.DomainPartition (Ch02.cubeDomain Q) :=
    Ch02.descendantsDomainPartition Q j
  have hRestricts : ∀ i : Pcell.Cell,
      Ch02.CoeffOn.RestrictsTo (F.coeffOn Q) (F.coeffOn i.1) := by
    intro i
    exact F.restrictsTo_of_subset
      (Homogenization.openCubeSet_subset_of_mem_descendantsAtDepth i.2)
  have hBlock := (Ch02.blockCoarseMatrixTheory
    (Ch02.cubeDomain Q) (F.coeffOn Q)).block_matrix_subadditive
      Pcell (fun i : Pcell.Cell => F.coeffOn i.1) hRestricts
  have hUpper := Ch04.matLoewnerLE_upperLeft_of_blockMatLoewnerLE hBlock
  have hParent :
      Ch02.bCoarse (Ch02.cubeDomain Q) (F.coeffOn Q) =
        aMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
      (Ch02.cubeDomain Q) (F.coeffOn Q)
      ((aCutoffTriadicData M L omega).onCube Q).isSymmetric
    exact hTheory.derived_matrices.2.2.trans hTheory.derived_matrices.1.symm
  have hChild : ∀ R : TriadicCube d,
      Ch02.bCoarse (Ch02.cubeDomain R) (F.coeffOn R) =
        aMatrix (Ch02.cubeDomain R) (F.coeffOn R) := by
    intro R
    have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
      (Ch02.cubeDomain R) (F.coeffOn R)
      ((aCutoffTriadicData M L omega).onCube R).isSymmetric
    exact hTheory.derived_matrices.2.2.trans hTheory.derived_matrices.1.symm
  change MatLoewnerLE
    (Ch02.bCoarse (Ch02.cubeDomain Q) (F.coeffOn Q))
    (Pcell.weightedMatAverage fun i =>
      Ch02.bCoarse (Ch02.cubeDomain i.1) (F.coeffOn i.1)) at hUpper
  rw [hParent] at hUpper
  have hWeighted :
      Pcell.weightedMatAverage (fun i =>
        Ch02.bCoarse (Ch02.cubeDomain i.1) (F.coeffOn i.1)) =
      Homogenization.descendantsAverageMat Q j (fun R =>
        aMatrix (Ch02.cubeDomain R) (F.coeffOn R)) := by
    rw [show (fun i : Pcell.Cell =>
        Ch02.bCoarse (Ch02.cubeDomain i.1) (F.coeffOn i.1)) =
        fun i => aMatrix (Ch02.cubeDomain i.1) (F.coeffOn i.1) by
      funext i
      exact hChild i.1]
    simpa [Pcell] using! Ch02.descendantsDomainPartition_weightedMatAverage Q j
      (fun R => aMatrix (Ch02.cubeDomain R) (F.coeffOn R))
  rw [hWeighted] at hUpper
  simpa [F, Pcell, aCutoffFamily, aCutoffTriadicData, randomAMatrix] using! hUpper

/-! ## The probe form as a pair of quadratic forms -/

private theorem vecDot_smul_matVecMul_smul' (A : Mat d) (c : ℝ) (v : Vec d) :
    vecDot (c • v) (matVecMul A (c • v)) =
      (c * c) * vecDot v (matVecMul A v) := by
  simp only [vecDot, matVecMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The probe form written through the two coarse quadratic forms. -/
theorem cutoffProbeForm_eq_quadratics (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (L : ℕ) {alpha : ℝ} (halpha : 0 < alpha) (R : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (v : Vec d) :
    cutoffProbeForm M L alpha R omega v =
      (1 / 2 : ℝ) * alpha⁻¹ *
          vecDot v (matVecMul (randomAMatrix M L (Ch02.cubeDomain R) omega) v) +
        (1 / 2 : ℝ) * alpha *
          vecDot v (matVecMul
            ((randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹) v) -
        vecDot v v := by
  have hsqrt : Real.sqrt alpha ≠ 0 := (Real.sqrt_pos.2 halpha).ne'
  have hinvsq : (Real.sqrt alpha)⁻¹ * (Real.sqrt alpha)⁻¹ = alpha⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt halpha.le]
  have hsq : Real.sqrt alpha * Real.sqrt alpha = alpha :=
    Real.mul_self_sqrt halpha.le
  have hcross : vecDot ((Real.sqrt alpha)⁻¹ • v) (Real.sqrt alpha • v) =
      vecDot v v := by
    simp only [vecDot, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  have hJ : cutoffProbeForm M L alpha R omega v =
      (1 / 2 : ℝ) *
          vecDot ((Real.sqrt alpha)⁻¹ • v)
            (matVecMul (randomAMatrix M L (Ch02.cubeDomain R) omega)
              ((Real.sqrt alpha)⁻¹ • v)) +
        (1 / 2 : ℝ) *
            vecDot (Real.sqrt alpha • v)
              (matVecMul ((randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹)
                (Real.sqrt alpha • v)) -
          vecDot ((Real.sqrt alpha)⁻¹ • v) (Real.sqrt alpha • v) := by
    simpa [cutoffProbeForm, cutoffResponseOnCube, aCutoffFamily,
      aCutoffTriadicData] using!
      cutoffResponseJ_eq_randomMatrixQuadratics M L (Ch02.cubeDomain R)
        ((Real.sqrt alpha)⁻¹ • v) (Real.sqrt alpha • v) omega
  rw [hJ, vecDot_smul_matVecMul_smul', vecDot_smul_matVecMul_smul', hcross,
    hinvsq, hsq]
  ring

/-! ## Averaging over descendants -/

theorem descendantsAverage_const (Q : TriadicCube d) (j : ℕ) (c : ℝ) :
    Homogenization.descendantsAverage Q j (fun _ => c) = c := by
  have hcard : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    have := Homogenization.descendantsAtDepth_card Q j
    rw [this]
    positivity
  simp only [Homogenization.descendantsAverage, Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem descendantsAverage_combo (Q : TriadicCube d) (j : ℕ)
    (c₁ c₂ c₃ : ℝ) (f g : TriadicCube d → ℝ) :
    Homogenization.descendantsAverage Q j
        (fun R => c₁ * f R + c₂ * g R - c₃) =
      c₁ * Homogenization.descendantsAverage Q j f +
        c₂ * Homogenization.descendantsAverage Q j g - c₃ := by
  have hcard : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    have := Homogenization.descendantsAtDepth_card Q j
    rw [this]
    positivity
  simp only [Homogenization.descendantsAverage, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- **Pathwise subdivision subadditivity of the probe form.** -/
theorem cutoffProbeForm_le_descendantsAverage
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {alpha : ℝ}
    (halpha : 0 < alpha) (Q : TriadicCube d) (j : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (v : Vec d) :
    cutoffProbeForm M L alpha Q omega v ≤
      Homogenization.descendantsAverage Q j
        (fun R => cutoffProbeForm M L alpha R omega v) := by
  have hprimal :=
    matLoewnerLE_randomAMatrix_descendantsAverage' M L omega Q j v
  have hdual :=
    matLoewnerLE_randomAStarInv_descendantsAverage M L omega Q j v
  have hA : vecDot v (matVecMul (randomAMatrix M L (Ch02.cubeDomain Q) omega) v)
      ≤ Homogenization.descendantsAverage Q j
        (fun R => vecDot v
          (matVecMul (randomAMatrix M L (Ch02.cubeDomain R) omega) v)) := by
    rw [← Homogenization.vecDot_matVecMul_descendantsAverageMat]
    linarith [hprimal]
  have hB : vecDot v
        (matVecMul ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹) v) ≤
      Homogenization.descendantsAverage Q j
        (fun R => vecDot v
          (matVecMul ((randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹) v)) := by
    rw [← Homogenization.vecDot_matVecMul_descendantsAverageMat]
    linarith [hdual]
  have havg : Homogenization.descendantsAverage Q j
      (fun R => cutoffProbeForm M L alpha R omega v) =
      (1 / 2 : ℝ) * alpha⁻¹ *
          Homogenization.descendantsAverage Q j
            (fun R => vecDot v
              (matVecMul (randomAMatrix M L (Ch02.cubeDomain R) omega) v)) +
        (1 / 2 : ℝ) * alpha *
          Homogenization.descendantsAverage Q j
            (fun R => vecDot v
              (matVecMul
                ((randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹) v)) -
        vecDot v v := by
    rw [show (fun R : TriadicCube d => cutoffProbeForm M L alpha R omega v) =
        fun R : TriadicCube d =>
          (1 / 2 : ℝ) * alpha⁻¹ *
              vecDot v
                (matVecMul (randomAMatrix M L (Ch02.cubeDomain R) omega) v) +
            (1 / 2 : ℝ) * alpha *
              vecDot v (matVecMul
                ((randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹) v) -
            vecDot v v by
      funext R
      exact cutoffProbeForm_eq_quadratics M L halpha R omega v]
    exact descendantsAverage_combo Q j _ _ _ _ _
  rw [cutoffProbeForm_eq_quadratics M L halpha Q omega v, havg]
  have h1 : (0 : ℝ) ≤ (1 / 2 : ℝ) * alpha⁻¹ := by positivity
  have h2 : (0 : ℝ) ≤ (1 / 2 : ℝ) * alpha := by positivity
  have := mul_le_mul_of_nonneg_left hA h1
  have := mul_le_mul_of_nonneg_left hB h2
  linarith

theorem descendantsAverage_half_sum (Q : TriadicCube d) (k : ℕ)
    (f g h : TriadicCube d → ℝ) :
    Homogenization.descendantsAverage Q k
        (fun R => (1 / 2 : ℝ) * (f R + g R + h R)) =
      (1 / 2 : ℝ) * (Homogenization.descendantsAverage Q k f +
        Homogenization.descendantsAverage Q k g +
        Homogenization.descendantsAverage Q k h) := by
  simp only [Homogenization.descendantsAverage, ← Finset.mul_sum,
    Finset.sum_add_distrib]
  ring

theorem descendantsAverage_finsetSum {iota : Type*} (Q : TriadicCube d)
    (k : ℕ) (s : Finset iota) (F : iota → TriadicCube d → ℝ) :
    Homogenization.descendantsAverage Q k (fun R => ∑ i ∈ s, F i R) =
      ∑ i ∈ s, Homogenization.descendantsAverage Q k (F i) := by
  simp only [Homogenization.descendantsAverage, Finset.mul_sum]
  exact Finset.sum_comm

/-- **Pathwise subdivision subadditivity of the finite probe sum.** -/
theorem finiteProbeSum_le_descendantsAverage
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {alpha : ℝ}
    (halpha : 0 < alpha) (Q : TriadicCube d) (k : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    finiteProbeSum M L alpha Q omega ≤
      Homogenization.descendantsAverage Q k
        (fun R => finiteProbeSum M L alpha R omega) := by
  classical
  have hexpand : Homogenization.descendantsAverage Q k
      (fun R => finiteProbeSum M L alpha R omega) =
      ∑ i : Fin d, ∑ j : Fin d,
        Homogenization.descendantsAverage Q k (fun R => (1 / 2 : ℝ) *
          (cutoffProbeForm M L alpha R omega
              ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
            cutoffProbeForm M L alpha R omega
              (Pi.single i (1 : ℝ) : Vec d) +
            cutoffProbeForm M L alpha R omega
              (Pi.single j (1 : ℝ) : Vec d))) := by
    rw [show (fun R : TriadicCube d => finiteProbeSum M L alpha R omega) =
        fun R : TriadicCube d => ∑ i : Fin d, ∑ j : Fin d, (1 / 2 : ℝ) *
          (cutoffProbeForm M L alpha R omega
              ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
            cutoffProbeForm M L alpha R omega
              (Pi.single i (1 : ℝ) : Vec d) +
            cutoffProbeForm M L alpha R omega
              (Pi.single j (1 : ℝ) : Vec d)) from rfl]
    rw [descendantsAverage_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact descendantsAverage_finsetSum Q k Finset.univ _
  rw [hexpand]
  simp only [finiteProbeSum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [descendantsAverage_half_sum]
  have h1 := cutoffProbeForm_le_descendantsAverage M L halpha Q k omega
    ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d))
  have h2 := cutoffProbeForm_le_descendantsAverage M L halpha Q k omega
    (Pi.single i (1 : ℝ) : Vec d)
  have h3 := cutoffProbeForm_le_descendantsAverage M L halpha Q k omega
    (Pi.single j (1 : ℝ) : Vec d)
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
