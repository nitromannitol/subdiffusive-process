module

public import SubdiffusiveProcess.CoarseGrainingVocab.AhomStarCharacterization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ResponseMeasureTheory
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepDualPrefixSuffix

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open scoped Matrix.Norms.Elementwise

noncomputable section


variable {d : ℕ}

/-! ## Stationarity of the dual annealed matrix -/

theorem randomAStarInv_eq_originCube_translatePotentialSequence
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) :
    (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ =
      (randomAStarMatrix M L
        (Ch02.cubeDomain (Homogenization.originCube d Q.scale))
        (translatePotentialSequence (Homogenization.triadicCubeShift Q) omega))⁻¹ := by
  rw [randomAStarInv_eq_rawSigmaStarInvCoarse,
    randomAStarInv_eq_rawSigmaStarInvCoarse]
  rw [Homogenization.openCubeSet_eq_translateSet_originCube_of_triadicCube Q]
  rw [Homogenization.sigmaStarInvCoarse_translateSet_eq_translateCoeffField]
  apply congrArg (Homogenization.sigmaStarInvCoarse
    (Homogenization.openCubeSet (Homogenization.originCube d Q.scale)))
  funext x
  change Homogenization.scalarMatrix
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega
        (x + Homogenization.triadicCubeShift Q)) =
    Homogenization.scalarMatrix
      (_root_.SubdiffusiveProcess.Model.aCutoff M L
        (translatePotentialSequence (Homogenization.triadicCubeShift Q) omega) x)
  exact congrArg Homogenization.scalarMatrix
    (aCutoff_translatePotentialSequence M L
      (Homogenization.triadicCubeShift Q) omega x).symm

theorem abarStarInv_cube_eq_originCube
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (Q : TriadicCube d) :
    abarStarInv M L (Ch02.cubeDomain Q) =
      abarStarInv M L
        (Ch02.cubeDomain (Homogenization.originCube d Q.scale)) := by
  unfold abarStarInv
  calc
    ∫ omega, (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹
        ∂M.P.toMeasure =
        ∫ omega, (randomAStarMatrix M L
          (Ch02.cubeDomain (Homogenization.originCube d Q.scale))
          (translatePotentialSequence (Homogenization.triadicCubeShift Q) omega))⁻¹
          ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      exact randomAStarInv_eq_originCube_translatePotentialSequence M L omega Q
    _ = ∫ omega, (randomAStarMatrix M L
          (Ch02.cubeDomain (Homogenization.originCube d Q.scale)) omega)⁻¹
          ∂M.P.toMeasure := by
      have hmap := potentialSequenceLaw_stationary M (Homogenization.triadicCubeShift Q)
      have hg : AEStronglyMeasurable
          (fun omega => (randomAStarMatrix M L
            (Ch02.cubeDomain (Homogenization.originCube d Q.scale)) omega)⁻¹)
          (Measure.map (translatePotentialSequence (Homogenization.triadicCubeShift Q))
            M.P.toMeasure) := by
        rw [hmap]
        exact (integrable_randomAStarMatrix_inv M L
          (Ch02.cubeDomain (Homogenization.originCube d Q.scale))).aestronglyMeasurable
      have h := integral_map
        (measurable_translatePotentialSequence (Homogenization.triadicCubeShift Q)).aemeasurable hg
      rw [hmap] at h
      simpa only [Function.comp_def] using! h.symm


theorem matLoewnerLE_randomAStarInv_descendantsAverage
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (j : ℕ) :
    MatLoewnerLE ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹)
      (Homogenization.descendantsAverageMat Q j fun R =>
        (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹) := by
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
  have hLower := Ch04.matLoewnerLE_lowerRight_of_blockMatLoewnerLE hBlock
  have hIdent : ∀ R : TriadicCube d,
      (Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R)).lowerRight =
        (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ := by
    intro R
    rw [Ch02.coarseBlockMatrix_lowerRight]
    rw [randomAStarInv_eq_rawSigmaStarInvCoarse]
    rfl
  change MatLoewnerLE
    ((Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)).lowerRight)
    (Pcell.weightedMatAverage fun i =>
      (Ch02.coarseBlockMatrix (Ch02.cubeDomain i.1) (F.coeffOn i.1)).lowerRight)
    at hLower
  rw [hIdent Q] at hLower
  have hWeighted :
      Pcell.weightedMatAverage (fun i =>
        (Ch02.coarseBlockMatrix (Ch02.cubeDomain i.1) (F.coeffOn i.1)).lowerRight) =
      Homogenization.descendantsAverageMat Q j (fun R =>
        (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹) := by
    rw [show (fun i : Pcell.Cell =>
        (Ch02.coarseBlockMatrix (Ch02.cubeDomain i.1) (F.coeffOn i.1)).lowerRight) =
        fun i => (randomAStarMatrix M L (Ch02.cubeDomain i.1) omega)⁻¹ by
      funext i
      exact hIdent i.1]
    simpa [Pcell] using! Ch02.descendantsDomainPartition_weightedMatAverage Q j
      (fun R => (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹)
  rw [hWeighted] at hLower
  exact hLower

/-! ## Annealed transport -/

theorem integrable_randomAStarInv_quadratic
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p : Vec d) :
    Integrable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      (1 / 2 : ℝ) * vecDot p
        (matVecMul ((randomAStarMatrix M L U omega)⁻¹) p)) M.P.toMeasure := by
  apply Integrable.const_mul
  simp only [vecDot, matVecMul]
  apply integrable_finsetSum Finset.univ
  intro i _hi
  apply Integrable.const_mul
  apply integrable_finsetSum Finset.univ
  intro j _hj
  exact (((integrable_randomAStarMatrix_inv M L U).eval i).eval j).mul_const (p j)

theorem integral_randomAStarInv_quadratic
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p : Vec d) :
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        (1 / 2 : ℝ) * vecDot p
          (matVecMul ((randomAStarMatrix M L U omega)⁻¹) p) ∂M.P.toMeasure =
      (1 / 2 : ℝ) * vecDot p (matVecMul (abarStarInv M L U) p) := by
  rw [MeasureTheory.integral_const_mul]
  congr 1
  unfold abarStarInv
  simp only [vecDot, matVecMul]
  rw [integral_finsetSum Finset.univ]
  · congr 1
    ext i
    rw [MeasureTheory.integral_const_mul]
    rw [integral_finsetSum Finset.univ]
    · simp_rw [MeasureTheory.integral_mul_const]
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      congr 1
      exact (integral_matrix_apply (integrable_randomAStarMatrix_inv M L U) i j).symm
    · intro j _hj
      exact (((integrable_randomAStarMatrix_inv M L U).eval i).eval j).mul_const (p j)
  · intro i _hi
    apply Integrable.const_mul
    apply integrable_finsetSum Finset.univ
    intro j _hj
    exact (((integrable_randomAStarMatrix_inv M L U).eval i).eval j).mul_const (p j)

theorem descendantsAverageMat_congr' (Q : TriadicCube d) (j : ℕ)
    {F G : TriadicCube d → Mat d}
    (h : ∀ R ∈ Homogenization.descendantsAtDepth Q j, F R = G R) :
    Homogenization.descendantsAverageMat Q j F =
      Homogenization.descendantsAverageMat Q j G := by
  funext i k
  simp only [Homogenization.descendantsAverageMat,
    Homogenization.descendantsAverage]
  congr 1
  apply Finset.sum_congr rfl
  intro R hR
  rw [h R hR]

theorem descendantsAverageMat_const' (Q : TriadicCube d) (j : ℕ) (A : Mat d) :
    Homogenization.descendantsAverageMat Q j (fun _ => A) = A := by
  funext i k
  simp only [Homogenization.descendantsAverageMat,
    Homogenization.descendantsAverage]
  have hcard : ((Homogenization.descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr
      (Homogenization.descendantsAtDepth_nonempty Q j)
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

/-! ## Annealed dual subadditivity, antitonicity, and the limit comparison -/

theorem matLoewnerLE_abarStarInv_descendantsAverage
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (j : ℕ) :
    MatLoewnerLE (abarStarInv M L (Ch02.cubeDomain Q))
      (Homogenization.descendantsAverageMat Q j fun R =>
        abarStarInv M L (Ch02.cubeDomain R)) := by
  intro p
  rw [← integral_randomAStarInv_quadratic M L (Ch02.cubeDomain Q) p]
  rw [show (1 / 2 : ℝ) * vecDot p
      (matVecMul (Homogenization.descendantsAverageMat Q j fun R =>
        abarStarInv M L (Ch02.cubeDomain R)) p) =
      ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (Homogenization.descendantsAverageMat Q j fun R =>
            (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹) p)
          ∂M.P.toMeasure by
    calc
      (1 / 2 : ℝ) * vecDot p
          (matVecMul (Homogenization.descendantsAverageMat Q j fun R =>
            abarStarInv M L (Ch02.cubeDomain R)) p) =
        Homogenization.descendantsAverage Q j (fun R =>
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (abarStarInv M L (Ch02.cubeDomain R)) p)) := by
          rw [Homogenization.vecDot_matVecMul_descendantsAverageMat]
          simp only [Homogenization.descendantsAverage]
          rw [← Finset.mul_sum]
          ring
      _ = Homogenization.descendantsAverage Q j (fun R =>
          ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
            (1 / 2 : ℝ) * vecDot p
              (matVecMul ((randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹) p)
              ∂M.P.toMeasure) := by
          congr 1
          funext R
          exact (integral_randomAStarInv_quadratic M L (Ch02.cubeDomain R) p).symm
      _ = ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          Homogenization.descendantsAverage Q j (fun R =>
            (1 / 2 : ℝ) * vecDot p
              (matVecMul ((randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹) p))
            ∂M.P.toMeasure := by
          simp only [Homogenization.descendantsAverage]
          rw [MeasureTheory.integral_const_mul]
          rw [integral_finsetSum]
          intro R _hR
          exact integrable_randomAStarInv_quadratic M L (Ch02.cubeDomain R) p
      _ = ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (Homogenization.descendantsAverageMat Q j fun R =>
              (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹) p)
            ∂M.P.toMeasure := by
          apply integral_congr_ae
          filter_upwards with omega
          rw [Homogenization.vecDot_matVecMul_descendantsAverageMat]
          simp only [Homogenization.descendantsAverage]
          rw [← Finset.mul_sum]
          ring]
  refine integral_mono
    (integrable_randomAStarInv_quadratic M L (Ch02.cubeDomain Q) p) ?_
    (fun omega => matLoewnerLE_randomAStarInv_descendantsAverage M L omega Q j p)
  simp only [Homogenization.vecDot_matVecMul_descendantsAverageMat,
    Homogenization.descendantsAverage]
  apply Integrable.const_mul
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro R _hR
  have := integrable_randomAStarInv_quadratic M L (Ch02.cubeDomain R) p
  simpa using! this.const_mul (2 : ℝ)

theorem matLoewnerLE_abarStarInv_originCube_succ
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    MatLoewnerLE
      (abarStarInv M L
        (Ch02.cubeDomain (Homogenization.originCube d ((n + 1 : ℕ) : ℤ))))
      (abarStarInv M L
        (Ch02.cubeDomain (Homogenization.originCube d (n : ℤ)))) := by
  let Q : TriadicCube d := Homogenization.originCube d ((n + 1 : ℕ) : ℤ)
  have hSub := matLoewnerLE_abarStarInv_descendantsAverage M L Q 1
  have hAverage :
      Homogenization.descendantsAverageMat Q 1 (fun R =>
        abarStarInv M L (Ch02.cubeDomain R)) =
      abarStarInv M L
        (Ch02.cubeDomain (Homogenization.originCube d (n : ℤ))) := by
    calc
      Homogenization.descendantsAverageMat Q 1 (fun R =>
          abarStarInv M L (Ch02.cubeDomain R)) =
        Homogenization.descendantsAverageMat Q 1 (fun _ =>
          abarStarInv M L
            (Ch02.cubeDomain (Homogenization.originCube d (n : ℤ)))) := by
          apply descendantsAverageMat_congr'
          intro R hR
          have hscale : R.scale = (n : ℤ) := by
            rw [Homogenization.scale_eq_sub_of_mem_descendantsAtDepth hR]
            change ((n : ℤ) + 1) - 1 = (n : ℤ)
            omega
          calc
            abarStarInv M L (Ch02.cubeDomain R) =
                abarStarInv M L (Ch02.cubeDomain
                  (Homogenization.originCube d R.scale)) :=
              abarStarInv_cube_eq_originCube M L R
            _ = abarStarInv M L (Ch02.cubeDomain
                  (Homogenization.originCube d (n : ℤ))) := by rw [hscale]
      _ = abarStarInv M L
            (Ch02.cubeDomain (Homogenization.originCube d (n : ℤ))) :=
          descendantsAverageMat_const' Q 1 _
  rwa [hAverage] at hSub

/-- **The dual of `antitone_abarScalarReadout`.** -/
theorem antitone_oneStepAnnealedDualReadout [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    Antitone (oneStepAnnealedDualReadout M L) := by
  have hstep : ∀ n : ℕ,
      oneStepAnnealedDualReadout M L (n + 1) ≤
        oneStepAnnealedDualReadout M L n := by
    intro n
    have h := matLoewnerLE_abarStarInv_originCube_succ M L n
    have hQ := abarStarInv_originCube_eq_oneStepAnnealedDualReadout_smul_one
      M L (n + 1)
    have hn := abarStarInv_originCube_eq_oneStepAnnealedDualReadout_smul_one M L n
    rw [hQ, hn] at h
    have hx := h (Pi.single (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d) 1)
    simpa [matVecMul_single, vecDot_single_left, Matrix.one_apply] using! hx
  intro a b hab
  induction hab with
  | refl => exact le_rfl
  | @step k hak ih => exact le_trans (hstep k) ih

/-- **Step 3's missing inequality, delivered:** `v ≥ 1`. -/
theorem ahom_inv_le_oneStepAnnealedDualReadout [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (j : ℕ) :
    (ahom M L)⁻¹ ≤ oneStepAnnealedDualReadout M L j := by
  have hlim := tendsto_abarStarInv_originCube M L
  have hscalar : ∀ k : ℕ,
      abarStarInv M L (Ch02.cubeDomain (Homogenization.originCube d (k : ℤ))) =
        oneStepAnnealedDualReadout M L k • (1 : Mat d) :=
    fun k => abarStarInv_originCube_eq_oneStepAnnealedDualReadout_smul_one M L k
  let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  have hentry : Filter.Tendsto (fun k : ℕ => oneStepAnnealedDualReadout M L k)
      Filter.atTop (nhds ((ahom M L)⁻¹)) := by
    have h0 := (tendsto_pi_nhds.mp hlim) i
    have h1 := (tendsto_pi_nhds.mp h0) i
    simpa [hscalar, Matrix.one_apply, Matrix.smul_apply] using! h1
  refine le_of_tendsto hentry ?_
  filter_upwards [Filter.eventually_ge_atTop j] with k hk
  exact antitone_oneStepAnnealedDualReadout M L hk

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
