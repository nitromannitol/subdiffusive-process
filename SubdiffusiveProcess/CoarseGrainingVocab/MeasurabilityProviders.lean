module

public import SubdiffusiveProcess.CoarseGrainingVocab.Model
public import SubdiffusiveProcess.Assumptions.PotentialField
public import Homogenization.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability
public import Homogenization.Probability.RandomField

@[expose] public section

/-!
# Measurability providers for the random coarse matrix

This file supplies the coefficient-independent dense-family and fixed-competitor
measurability inputs needed to make the finite-volume cutoff coarse matrix an
honest random matrix.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal

noncomputable section

/-- Joint measurability of the finite cutoff in the sample and spatial variables. -/
theorem measurable_cutoff_uncurry {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    Measurable (fun z : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L z.1 z.2) := by
  have hEvalSwap : Measurable
      (Function.uncurry fun x : Vec d =>
        fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => g x) := by
    exact measurable_uncurry_of_continuous_of_measurable
      (ι := Vec d) (α := SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) (β := ℝ)
      (fun g => g.1.1.continuous)
      (fun x => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x)
  have hEval : Measurable
      (fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d × Vec d => q.1 q.2) :=
    hEvalSwap.comp measurable_swap
  apply Measurable.exp
  apply Finset.measurable_sum
  intro k _hk
  have hCoordinate : Measurable
      (fun z : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d => (z.1 k, z.2)) :=
    ((measurable_pi_apply k).comp measurable_fst).prodMk measurable_snd
  exact (hEval.comp hCoordinate).sub measurable_const

private theorem blockEnergyDensity_scalarCoeffField {d : ℕ}
    (a : Vec d → ℝ) (ha : ∀ x, 0 < a x) (X : BlockState d) (x : Vec d) :
    blockEnergyDensity (scalarCoeffField a) X x =
      (1 / 2 : ℝ) *
        (a x * vecDot (X.potential x) (X.potential x) +
          (a x)⁻¹ * vecDot (X.flux x) (X.flux x)) := by
  have hInv : ((Homogenization.scalarMatrix (d := d) (a x))⁻¹ : Mat d) =
      Homogenization.scalarMatrix (d := d) (a x)⁻¹ := by
    rw [Homogenization.scalarMatrix,
      Homogenization.nonsing_inv_smul (a x) (ha x).ne' (by simp)]
    simp [Homogenization.scalarMatrix]
  simp [blockEnergyDensity, blockCoeffField, blockMatrixOfCoeff,
    scalarCoeffField, Homogenization.Book.Ch02.symmPart_scalarMatrix,
    Homogenization.Book.Ch02.skewPart_scalarMatrix, hInv,
    BlockState.eval, blockMatVecMul, Homogenization.matVecMul_scalarMatrix,
    Homogenization.blockVecDot, Homogenization.matVecMul,
    Homogenization.vecDot, Homogenization.matTranspose, Finset.mul_sum,
    mul_left_comm]

/-- For a fixed admissible competitor, its cutoff block-energy average is a
measurable function of the potential sample. -/
theorem measurable_cutoff_fixed_blockEnergyAverage {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (P : BlockVec d) (X : BlockState d)
    (hX : IsBlockMuAdmissible (U : Set (Vec d)) P X) :
    Measurable (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      blockEnergyAverage (U : Set (Vec d))
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) X) := by
  have hJoint := measurable_cutoff_uncurry M L
  have hXL2 : MemBlockL2 (U : Set (Vec d)) X.eval := hX.memBlockL2_eval
  have hPotentialL2 : MemVectorL2 (U : Set (Vec d)) X.potential := by
    simpa [BlockState.eval] using
      memVectorL2_fst_of_memBlockL2 (U := (U : Set (Vec d))) hXL2
  have hFluxL2 : MemVectorL2 (U : Set (Vec d)) X.flux := by
    simpa [BlockState.eval] using
      memVectorL2_snd_of_memBlockL2 (U := (U : Set (Vec d))) hXL2
  let f : Vec d → Vec d := hPotentialL2.aestronglyMeasurable.mk X.potential
  let g : Vec d → Vec d := hFluxL2.aestronglyMeasurable.mk X.flux
  have hf : Measurable f := hPotentialL2.aestronglyMeasurable.measurable_mk
  have hg : Measurable g := hFluxL2.aestronglyMeasurable.measurable_mk
  have measurable_vecDot_self {v :
      SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d → Vec d}
      (hv : Measurable v) : Measurable (fun z => vecDot (v z) (v z)) := by
    simp only [vecDot]
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp hv).mul ((measurable_pi_apply i).comp hv)
  have hPotential : Measurable
      (fun z : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L z.1 z.2 *
          vecDot (f z.2) (f z.2)) := by
    exact hJoint.mul (measurable_vecDot_self (hf.comp measurable_snd))
  have hFlux : Measurable
      (fun z : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L z.1 z.2)⁻¹ *
          vecDot (g z.2) (g z.2)) := by
    exact hJoint.inv.mul (measurable_vecDot_self (hg.comp measurable_snd))
  have hIntegral : StronglyMeasurable
      (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        ∫ x, (1 / 2 : ℝ) *
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω x *
              vecDot (f x) (f x) +
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω x)⁻¹ *
              vecDot (g x) (g x))
          ∂volumeMeasureOn (U : Set (Vec d))) :=
    (measurable_const.mul (hPotential.add hFlux)).stronglyMeasurable.integral_prod_right'
  have hEq :
      (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        blockEnergyAverage (U : Set (Vec d))
          (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) X) =
      fun ω => (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ *
        ∫ x, (1 / 2 : ℝ) *
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω x *
              vecDot (f x) (f x) +
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω x)⁻¹ *
              vecDot (g x) (g x))
          ∂volumeMeasureOn (U : Set (Vec d)) := by
    funext ω
    rw [blockEnergyAverage, volumeAverage]
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hPotentialL2.aestronglyMeasurable.ae_eq_mk,
      hFluxL2.aestronglyMeasurable.ae_eq_mk] with x hfx hgx
    simpa [f, g, hfx, hgx] using
      blockEnergyDensity_scalarCoeffField
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L ω) X x
  rw [hEq]
  exact measurable_const.mul hIntegral.measurable

private structure CutoffEllipticityData {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (U : Ch02.Domain d) where
  lam : ℝ
  Lam : ℝ
  isElliptic : IsEllipticFieldOn lam Lam (U : Set (Vec d))
    (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω))

private theorem nonempty_cutoffEllipticityData {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (U : Ch02.Domain d) :
    Nonempty (CutoffEllipticityData M L ω U) := by
  let a := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω
  have ha_cont : Continuous a := SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L ω
  have hcompact : IsCompact (closure (U : Set (Vec d))) :=
    U.isBoundedDomain.isBounded.isCompact_closure
  have hnonempty : (closure (U : Set (Vec d))).Nonempty := U.nonempty.closure
  obtain ⟨xMin, hxMin, hMin⟩ :=
    hcompact.exists_isMinOn hnonempty ha_cont.continuousOn
  obtain ⟨xMax, hxMax, hMax⟩ :=
    hcompact.exists_isMaxOn hnonempty ha_cont.continuousOn
  refine ⟨{
    lam := a xMin
    Lam := a xMax
    isElliptic := ?_
  }⟩
  constructor
  · rw [measurable_pi_iff]
    intro i
    rw [measurable_pi_iff]
    intro j
    have hEntry : Measurable
        (fun x : Vec d => scalarCoeffField a x i j) := by
      have hMatrix : Continuous (fun x : Vec d => scalarCoeffField a x) :=
        ha_cont.smul continuous_const
      exact ((continuous_apply j).comp ((continuous_apply i).comp hMatrix)).measurable
    exact hEntry.piecewise U.measurableSet measurable_const
  · intro x hx
    exact (isEllipticMatrix_scalarMatrix (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L ω x)).mono
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L ω xMin)
      (hMin (subset_closure hx)) (hMax (subset_closure hx))

private noncomputable def cutoffEllipticityData {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (U : Ch02.Domain d) :
    CutoffEllipticityData M L ω U :=
  Classical.choice (nonempty_cutoffEllipticityData M L ω U)

private noncomputable def domainMuRecoveryData {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) : PotentialSolenoidalL2RecoveryData (U : Set (Vec d)) :=
  potentialSolenoidalL2RecoveryData_ofSubmoduleClosures_of_potentialZeroTraceClosureRealization
    (PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      U.isDomain)

private theorem mu_eq_domainMuCandidate {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (U : Ch02.Domain d) :
    ∀ P : BlockVec d,
      Mu (U : Set (Vec d)) P
          (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) =
        ((domainMuRecoveryData U).toMuHilbertRealization
          ((domainMuRecoveryData U).toMuOperatorSystemDataOfIsEllipticFieldOn
            (cutoffEllipticityData M L ω U).isElliptic
            (Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U))).muCandidate P := by
  let Uset : Set (Vec d) := (U : Set (Vec d))
  let a : CoeffField d := scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
  let R : PotentialSolenoidalL2RecoveryData Uset := domainMuRecoveryData U
  let E := cutoffEllipticityData M L ω U
  let hvol : 0 < (volume Uset).toReal :=
    Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U
  let system : MuOperatorSystemData Uset a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn E.isElliptic hvol
  intro P
  have hCandidateLe :
      ∀ X : BlockState d, IsBlockMuAdmissible Uset P X →
        (R.toMuHilbertRealization system).muCandidate P ≤ blockEnergyAverage Uset a X := by
    intro X hX
    let Y : CorrectionFieldData Uset := hX.toCorrectionFieldDataOfAdmissible
    have hXmem : MemBlockL2 Uset X.eval := hX.memBlockL2_eval
    have hcorr :
        Y.toHilbertBlockL2 ∈
          R.toPotentialSolenoidalL2Data.toMuCorrectionSpaceData.correctionSpace :=
      R.toPotentialSolenoidalL2Data.toMuCorrectionSpaceData.mem_correctionSpace
        Y.potential_memL2 Y.flux_memL2 Y.isPotentialZeroTrace
        Y.isSolenoidalZeroNormalTrace
    have hsplit :
        toHilbertBlockL2OfBlockField (U := Uset) hXmem =
          blockVecToHilbertBlockL2Const (U := Uset) P + Y.toHilbertBlockL2 := by
      simpa [Y] using
        hX.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
    have hcorr_mem :
        toHilbertBlockL2OfBlockField (U := Uset) hXmem -
            (R.toMuHilbertRealization system).constantField P ∈
          (R.toMuHilbertRealization system).correctionSpace.correctionSpace := by
      rw [hsplit]
      simpa [R, system, PotentialSolenoidalL2RecoveryData.toMuHilbertRealization,
        MuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcorr
    have hMin :
        (R.toMuHilbertRealization system).muCandidate P ≤
          quadraticEnergy
            (energyBilinOfOperator system.toMuOperatorRealization.operator)
            (toHilbertBlockL2OfBlockField (U := Uset) hXmem) := by
      simpa [R, system, PotentialSolenoidalL2RecoveryData.toMuHilbertRealization,
        MuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
        (R.toMuHilbertRealization system).muCandidate_le_quadraticEnergy P
          (toHilbertBlockL2OfBlockField (U := Uset) hXmem) hcorr_mem
    calc
      (R.toMuHilbertRealization system).muCandidate P ≤
          quadraticEnergy
            (energyBilinOfOperator system.toMuOperatorRealization.operator)
            (toHilbertBlockL2OfBlockField (U := Uset) hXmem) := hMin
      _ = blockEnergyAverage Uset a X :=
        system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState hXmem
  have hrecEnergy :
      blockEnergyAverage Uset a
          ((R.toMuCorrectionSpaceRecoveryData).recoveredField system P) =
        (R.toMuHilbertRealization system).muCandidate P := by
    let H : MuHilbertRealization Uset a := R.toMuHilbertRealization system
    have hminim :
        toHilbertBlockL2OfBlockField (U := Uset)
            ((R.toMuCorrectionSpaceRecoveryData).recoveredField_memBlockL2 system P) =
          H.minimizerMap P := by
      simpa [H, R, system, PotentialSolenoidalL2RecoveryData.toMuHilbertRealization] using!
        (R.toMuCorrectionSpaceRecoveryData).recoveredField_minimizer_eq system P
    calc
      blockEnergyAverage Uset a
          ((R.toMuCorrectionSpaceRecoveryData).recoveredField system P) =
          quadraticEnergy
            (energyBilinOfOperator system.toMuOperatorRealization.operator)
            (toHilbertBlockL2OfBlockField (U := Uset)
              ((R.toMuCorrectionSpaceRecoveryData).recoveredField_memBlockL2 system P)) := by
        symm
        exact system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
          ((R.toMuCorrectionSpaceRecoveryData).recoveredField_memBlockL2 system P)
      _ = quadraticEnergy H.energyBilin (H.minimizerMap P) := by
        rw [hminim]
        rfl
      _ = H.muCandidate P := rfl
      _ = (R.toMuHilbertRealization system).muCandidate P := rfl
  have hBddBelow : BddBelow (muValueSet Uset P a) := by
    refine ⟨vecDot P.1 P.2, ?_⟩
    intro value hvalue
    rcases hvalue with ⟨X, hX, rfl⟩
    exact hX.blockEnergyAverage_ge_vecDot_of_integral_eq_zero_of_isEllipticFieldOn
      (a := a) (hX.toBlockMuIntegrabilityDataOfIsEllipticFieldOn E.isElliptic)
      E.isElliptic
      (by simpa [sub_eq_add_neg] using
        (IsPotentialZeroTraceOn.integral_eq_zero hX.isPotentialZeroTrace))
      (by simpa [sub_eq_add_neg] using
        (IsSolenoidalZeroNormalTraceOn.integral_eq_zero U.isDomain.isSobolevRegularDomain
          hX.isSolenoidalZeroNormalTrace))
      hvol.ne'
  have hUpper :
      Mu Uset P a ≤ (R.toMuHilbertRealization system).muCandidate P := by
    let Xrec : BlockState d :=
      (R.toMuCorrectionSpaceRecoveryData).recoveredField system P
    have hAdm : IsBlockMuAdmissible Uset P Xrec := by
      simpa [Xrec] using
        (R.toMuCorrectionSpaceRecoveryData).recoveredField_admissible system P
    calc
      Mu Uset P a ≤ blockEnergyAverage Uset a Xrec :=
        csInf_le hBddBelow (muValueSet_mem hAdm)
      _ = (R.toMuHilbertRealization system).muCandidate P := hrecEnergy
  have hLower :
      (R.toMuHilbertRealization system).muCandidate P ≤ Mu Uset P a := by
    apply le_Mu_of_forall_isBlockMuAdmissible
    intro X hX
    exact hCandidateLe X hX
  exact le_antisymm hUpper hLower

/-- A single countable family of admissible competitors, depending on the
domain and loading but not on the cutoff realization, computes every cutoff
`Mu` value. -/
theorem cutoffMu_countableReduction {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (P : BlockVec d) :
    ∃ X : ℕ → BlockState d,
      (∀ n, IsBlockMuAdmissible (U : Set (Vec d)) P (X n)) ∧
      ∀ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
        Mu (U : Set (Vec d)) P
            (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) =
          ⨅ n : ℕ,
            blockEnergyAverage (U : Set (Vec d))
              (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) (X n) := by
  let R : PotentialSolenoidalL2RecoveryData (U : Set (Vec d)) := domainMuRecoveryData U
  let Rc : MuCorrectionSpaceRecoveryData (U : Set (Vec d)) :=
    R.toMuCorrectionSpaceRecoveryData
  letI : Fact ((1 : ENNReal) ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  letI : TopologicalSpace.SeparableSpace ↥Rc.correctionSpace := by infer_instance
  let X : ℕ → BlockState d := fun n =>
    Rc.affineField P (TopologicalSpace.denseSeq ↥Rc.correctionSpace n)
  refine ⟨X, ?_, ?_⟩
  · intro n
    exact Rc.affineField_admissible P (TopologicalSpace.denseSeq ↥Rc.correctionSpace n)
  · intro ω
    let E := cutoffEllipticityData M L ω U
    let system : MuOperatorSystemData (U : Set (Vec d))
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) :=
      R.toMuOperatorSystemDataOfIsEllipticFieldOn E.isElliptic
        (Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U)
    have hMu : ∀ Q : BlockVec d,
        Mu (U : Set (Vec d)) Q
            (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) =
          (R.toMuHilbertRealization system).muCandidate Q := by
      simpa [R, E, system] using mu_eq_domainMuCandidate M L ω U
    simpa [X, Rc, R, PotentialSolenoidalL2RecoveryData.toMuHilbertRealization] using
      Rc.Mu_eq_iInf_blockEnergyAverage_affineField_denseSeq system hMu P

/-- Every fixed deterministic doubled loading has measurable cutoff `Mu`. -/
theorem measurable_cutoff_Mu {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (P : BlockVec d) :
    Measurable (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      Mu (U : Set (Vec d)) P
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω))) := by
  obtain ⟨X, hX, hMu⟩ := cutoffMu_countableReduction M L U P
  have hEq :
      (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        Mu (U : Set (Vec d)) P
          (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω))) =
      fun ω => ⨅ n : ℕ,
        blockEnergyAverage (U : Set (Vec d))
          (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) (X n) := by
    funext ω
    exact hMu ω
  rw [hEq]
  exact Measurable.iInf fun n =>
    measurable_cutoff_fixed_blockEnergyAverage M L U P (X n) (hX n)

/-- Every fixed deterministic response probe of the scalar cutoff coefficient
is measurable in the potential sample. -/
theorem measurable_cutoff_responseJ {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p q : Vec d) :
    Measurable (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      J U (aCutoffCoeffOnData M L ω U).toCoeffOn p q) := by
  have hMu := measurable_cutoff_Mu M L U (-p, q)
  have hEq :
      (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        J U (aCutoffCoeffOnData M L ω U).toCoeffOn p q) =
      fun ω => Mu (U : Set (Vec d)) (-p, q)
          (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) - vecDot p q := by
    funext ω
    let aω := (aCutoffCoeffOnData M L ω U).toCoeffOn
    calc
      J U aω p q = Ch02.doubledMu U aω (-p, q) - vecDot p q :=
        Ch02.responseJ_eq_doubledMu_neg_left_sub_vecDot U aω p q
      _ = Mu (U : Set (Vec d)) (-p, q) aω.toCoeffField - vecDot p q := by
        rw [Ch02.doubledMu_eq_Mu]
      _ = Mu (U : Set (Vec d)) (-p, q)
          (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) - vecDot p q := rfl
  rw [hEq]
  exact hMu.sub measurable_const

/-- The finite-volume primal coarse matrix of the scalar cutoff is a genuine
matrix-valued random variable. -/
theorem measurable_randomAMatrix {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d) :
    Measurable (randomAMatrix M L U) := by
  suffices h : @Measurable (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
      (Fin d → Fin d → ℝ) inferInstance MeasurableSpace.pi
      (fun omega i j => randomAMatrix M L U omega i j) by
    simpa only using! h
  by_cases hd : d = 0
  · subst d
    rw [measurable_pi_iff]
    intro i
    exact Fin.elim0 i
  letI : NeZero d := ⟨hd⟩
  rw [measurable_pi_iff]
  intro i
  rw [measurable_pi_iff]
  intro j
  have zero_matVecMul (v : Vec d) : matVecMul (0 : Mat d) v = 0 := by
    ext k
    simp [matVecMul]
  by_cases hij : i = j
  · subst j
    have hprobe := measurable_cutoff_responseJ M L U (Pi.single i 1) 0
    have hEq :
        (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
          randomAMatrix M L U ω i i) =
        fun ω => 2 * J U (aCutoffCoeffOnData M L ω U).toCoeffOn
          (Pi.single i 1) 0 := by
      funext ω
      let hdata := aCutoffCoeffOnData M L ω U
      let aω := hdata.toCoeffOn
      have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U aω hdata.isSymmetric
      change Ch02.aCoarse U aω i i = 2 * J U aω (Pi.single i 1) 0
      rw [hTheory.derived_matrices.1]
      simp [Ch02.sigmaCoarse, Ch02.sigmaEntry,
        Ch02.canonicalSigmaCorrectedResponse, hTheory.kappa_eq_zero,
        zero_matVecMul, matVecMul_zero, vecDot_zero_right]
    rw [hEq]
    exact measurable_const.mul hprobe
  · have hprobeSum := measurable_cutoff_responseJ M L U
      (Pi.single i 1 + Pi.single j 1) 0
    have hprobeI := measurable_cutoff_responseJ M L U (Pi.single i 1) 0
    have hprobeJ := measurable_cutoff_responseJ M L U (Pi.single j 1) 0
    have hEq :
        (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
          randomAMatrix M L U ω i j) =
        fun ω =>
          J U (aCutoffCoeffOnData M L ω U).toCoeffOn
              (Pi.single i 1 + Pi.single j 1) 0 -
            J U (aCutoffCoeffOnData M L ω U).toCoeffOn (Pi.single i 1) 0 -
            J U (aCutoffCoeffOnData M L ω U).toCoeffOn (Pi.single j 1) 0 := by
      funext ω
      let hdata := aCutoffCoeffOnData M L ω U
      let aω := hdata.toCoeffOn
      have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U aω hdata.isSymmetric
      change Ch02.aCoarse U aω i j =
        J U aω (Pi.single i 1 + Pi.single j 1) 0 -
          J U aω (Pi.single i 1) 0 - J U aω (Pi.single j 1) 0
      rw [hTheory.derived_matrices.1]
      simp [Ch02.sigmaCoarse, Ch02.sigmaEntry, hij,
        Ch02.canonicalSigmaCorrectedResponse, hTheory.kappa_eq_zero,
        zero_matVecMul, matVecMul_zero, vecDot_zero_right]
    rw [hEq]
    exact (hprobeSum.sub hprobeI).sub hprobeJ

end

end SubdiffusiveProcess.CoarseGrainingVocab
