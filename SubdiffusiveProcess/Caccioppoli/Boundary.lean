import SubdiffusiveProcess.Caccioppoli.Parent
namespace SubdiffusiveProcess.Caccioppoli
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal
noncomputable section
variable {d : ℕ} [NeZero d]
theorem exists_boundary_caccioppoli_with_datum
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ}
        {x : Vec d} {g : Vec d → Vec d}
        (u h : H1Function (openCubeSet Q)) (c₀ : ℝ),
        (∀ R, Ch02.CoeffOn.IsSymmetric (a.coeffOn R)) →
        IsForcedEquation Q a u g →
        Ch01.LocalizedZeroTraceFunctionOn
          (openCubeSet Q) (openCubeAtScale x (Q.scale - 1))
          (fun y ↦ u.toFun y - h.toFun y) →
        volumeAverage (openCubeSet Q) h.toFun = c₀ →
        0 < s → s < 1 → 0 < t → t < 1 / 2 → s + t < 1 →
        x ∈ openCubeSet Q →
        ForceBesovRegularity Q (2 * t) g →
        ForceBesovRegularity Q (2 * t) h.grad →
        localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
          caccioppoliWithRHSPrefactor C Q a s t *
            (Ch02.lambdaS Q t a *
                Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                normalizedL2SqOnSet (openCubeSet Q)
                  (fun y ↦ u.toFun y - c₀) +
              Real.rpow t (-10 : ℝ) *
                Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2 +
              Real.rpow t (-2 : ℝ) * Ch02.LambdaS Q t a *
                scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad ^ 2) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hcacc⟩ :=
    exists_boundaryCaccioppoliEnergy_withBoundaryDatum d
  obtain ⟨Kp, hKp, hparent⟩ := exists_splitDirichlet_parent_le_printedBudgets d
  let Kd : ℝ := 4 * (25 * Real.exp 4) * max 1 (C₂ ^ 2)
  let Md : ℝ := 2 * (18 : ℝ) ^ d * Kd
  let M : ℝ := max 1 (2 * Kp + Md)
  let Cb : ℝ := max 1 C₁
  let C : ℝ := M * Cb
  have hKd0 : 0 ≤ Kd := by
    dsimp [Kd]
    positivity
  have hMd0 : 0 ≤ Md := by
    dsimp [Md]
    positivity
  have hM : 1 ≤ M := le_max_left _ _
  have hCb : 1 ≤ Cb := le_max_left _ _
  have hC : 0 < C := mul_pos (lt_of_lt_of_le zero_lt_one hM)
    (lt_of_lt_of_le zero_lt_one hCb)
  refine ⟨C, hC, ?_⟩
  intro Q a s t x g u h c₀ hsymm hu htrace hhMean hs hs₁ ht ht₄ hst hx hg hh
  have ht₂ : 2 * t < 1 := by linarith
  have hgL2 : MemVectorL2 (cubeSet Q) g :=
    memVectorL2_cubeSet_of_forceBesovRegularity hg
  let rho : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g :=
    zeroTraceDirichletCorrectorData_publicCoeffField Q a hgL2
  have hzeroL2 : MemVectorL2 (openCubeSet Q) (fun _ ↦ (0 : Vec d)) := by
    rw [MemVectorL2, volumeMeasureOn]
    exact MemLp.zero
  obtain ⟨w, hwh, rw, hrwValue, _hrwGrad⟩ :=
    exists_dirichletForcedCubeSolution_boundaryData_withGradient Q a h hzeroL2
  let v : DirichletForcedCubeSolution Q a g :=
    splitDirichletForcedCubeSolution rho w h hwh
  let r₀ : H10Function (openCubeSet Q) :=
    boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a) rho
  have hvhPoint : ∀ y,
      (r₀ + rw).toH1Function.toFun y = v.toH1.toFun y - h.toFun y := by
    intro y
    change r₀.toH1Function.toFun y + rw.toH1Function.toFun y = _
    rw [hrwValue y]
    dsimp [v, r₀]
    ring
  have hvhTrace : Ch01.LocalizedZeroTraceFunctionOn
      (openCubeSet Q) (openCubeAtScale x (Q.scale - 1))
      (fun y ↦ v.toH1.toFun y - h.toFun y) :=
    Section6SchauderDatum.localizedZeroTraceFunctionOn_of_memH10
      ⟨r₀ + rw, funext hvhPoint⟩
  have huvTraceRaw := Homogenization.localizedZeroTraceFunctionOn_sub htrace hvhTrace
  have huvTrace : Ch01.LocalizedZeroTraceFunctionOn
      (openCubeSet Q) (openCubeAtScale x (Q.scale - 1))
      (fun y ↦ u.toFun y - v.toH1.toFun y) :=
    Section6SchauderDatum.localizedZeroTraceFunctionOn_congr
      (fun y ↦ by ring) huvTraceRaw
  have hzeroReg : ForceBesovRegularity Q (2 * t) (fun _ ↦ (0 : Vec d)) :=
    forceBesovRegularity_zero Q (2 * t)
  have hvBoundary : dirichletBoundaryGradientField v = h.grad := by
    unfold dirichletBoundaryGradientField
    rfl
  have hvBoundaryReg : ForceBesovRegularity Q (2 * t)
      (dirichletBoundaryGradientField v) := by
    simpa only [hvBoundary] using hh
  have hraw := hcacc u v hu huvTrace hs hs₁ ht (by linarith only [ht₄]) hst
    (by positivity : 0 < 2 * t) ht₂ hg hvBoundaryReg hx
  have hp := hparent (rho := rho) (w := w) (u := u) (h := h) c₀ hwh hsymm
    hhMean ht ht₄ hg hh
  have hd := dirichletEnergyWithRHSRHS_two_mul_sq_le_printed
    (Q := Q) (a := a) (C := C₂) (t := t) (g := g) v hC₂.le ht ht₄ hg
      hvBoundaryReg
  let BU : ℝ := Ch02.lambdaS Q t a *
    Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
    normalizedL2SqOnSet (openCubeSet Q) (fun y ↦ u.toFun y - c₀)
  let BF : ℝ := Real.rpow t (-10 : ℝ) *
    Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
    scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2
  let BH : ℝ := Real.rpow t (-2 : ℝ) * Ch02.LambdaS Q t a *
    scaleNormalizedPositiveBesovVectorNormTwo Q (2 * t) h.grad ^ 2
  let B : ℝ := BU + BF + BH
  let P₁ : ℝ := caccioppoliWithRHSPrefactor Cb Q a s t
  have hlam0 : 0 ≤ Ch02.lambdaS Q t a :=
    (Ch02.lambdaSq_finite_pos Q a ht (by norm_num)).le
  have hBU0 : 0 ≤ BU := by
    dsimp [BU]
    exact mul_nonneg
      (mul_nonneg hlam0 (Real.rpow_nonneg (by norm_num) _))
      (normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet Q))
  have hBF0 : 0 ≤ BF := by
    dsimp [BF]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg ht.le _)
        (Real.rpow_nonneg hlam0 _)) (sq_nonneg _)
  have hBH0 : 0 ≤ BH := by
    dsimp [BH]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg ht.le _)
        (Ch02.LambdaSq_finite_nonneg Q a ht (by norm_num))) (sq_nonneg _)
  have hB0 : 0 ≤ B := by dsimp [B]; linarith only [hBU0, hBF0, hBH0]
  have hP₁ : 1 ≤ P₁ := by
    dsimp [P₁]
    exact one_le_caccioppoliWithRHSPrefactor hCb hs hs₁ ht hst
  have hP₁nonneg : 0 ≤ P₁ := le_trans zero_le_one hP₁
  have hprefBase : caccioppoliWithRHSPrefactor C₁ Q a s t ≤ P₁ := by
    have hmono := caccioppoliWithRHSPrefactor_mul_const_le_of_mul_constant_le
      (M := (1 : ℝ)) (C₁ := C₁) (C₂ := Cb) (Q := Q) (a := a)
      (s := s) (t := t) (by norm_num) hC₁.le (by
        dsimp [Cb]
        simpa only [one_mul] using (le_max_right (1 : ℝ) C₁))
      hs ht hst
    simpa only [one_mul, P₁] using hmono
  have hp' : Ch02.lambdaS Q t a *
        Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
        normalizedL2SqOnSet (openCubeSet Q)
          (fun y ↦ u.toFun y - v.toH1.toFun y) ≤ Kp * B := by
    simpa only [BU, BF, BH, B] using hp
  have hd' : dirichletEnergyWithRHSRHS C₂ Q a (2 * t) g v ^ 2 ≤
      Kd * (BF + BH) := by
    rw [hvBoundary] at hd
    simpa only [Kd, BF, BH] using hd
  have hdB : dirichletEnergyWithRHSRHS C₂ Q a (2 * t) g v ^ 2 ≤ Kd * B := by
    calc
      _ ≤ Kd * (BF + BH) := hd'
      _ ≤ Kd * B := by
        apply mul_le_mul_of_nonneg_left _ hKd0
        dsimp [B]
        linarith only [hBU0]
  have hscalePow : (3 : ℝ) ^ (-(2 * Q.scale)) =
      Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) := by
    rw [← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have hfirst : 2 * (P₁ *
      (Ch02.lambdaS Q t a * (3 : ℝ) ^ (-(2 * Q.scale)) *
        normalizedL2SqOnSet (openCubeSet Q)
          (fun y ↦ u.toFun y - v.toH1.toFun y))) ≤
      (2 * Kp) * P₁ * B := by
    rw [hscalePow]
    have htwoP : 0 ≤ (2 : ℝ) * P₁ :=
      mul_nonneg (by norm_num) hP₁nonneg
    calc
      _ = (2 * P₁) *
          (Ch02.lambdaS Q t a * Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
            normalizedL2SqOnSet (openCubeSet Q)
              (fun y ↦ u.toFun y - v.toH1.toFun y)) := by ring
      _ ≤ (2 * P₁) * (Kp * B) := mul_le_mul_of_nonneg_left hp' htwoP
      _ = (2 * Kp) * P₁ * B := by ring
  have hsecond : 2 * ((18 : ℝ) ^ d *
      dirichletEnergyWithRHSRHS C₂ Q a (2 * t) g v ^ 2) ≤
      Md * P₁ * B := by
    calc
      _ = (2 * (18 : ℝ) ^ d) *
          dirichletEnergyWithRHSRHS C₂ Q a (2 * t) g v ^ 2 := by ring
      _ ≤ (2 * (18 : ℝ) ^ d) * (Kd * B) :=
        mul_le_mul_of_nonneg_left hdB (by positivity)
      _ = Md * B := by dsimp [Md]; ring
      _ ≤ Md * P₁ * B := by
        have hBP : B ≤ P₁ * B := by
          calc B = 1 * B := by ring
               _ ≤ P₁ * B := mul_le_mul_of_nonneg_right hP₁ hB0
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hBP hMd0
  have htoM : (2 * Kp) * P₁ * B + Md * P₁ * B ≤ M * P₁ * B := by
    have hcoef : 2 * Kp + Md ≤ M := le_max_right 1 _
    calc
      _ = (2 * Kp + Md) * (P₁ * B) := by ring
      _ ≤ M * (P₁ * B) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg hP₁nonneg hB0)
      _ = M * P₁ * B := by ring
  have hpref : M * P₁ ≤ caccioppoliWithRHSPrefactor C Q a s t := by
    dsimp [P₁, C]
    exact caccioppoliWithRHSPrefactor_mul_const_le_of_mul_constant_le
      hM (le_trans zero_le_one hCb) le_rfl hs ht hst
  have hparentCarrier0 : 0 ≤ Ch02.lambdaS Q t a * (3 : ℝ) ^ (-(2 * Q.scale)) *
      normalizedL2SqOnSet (openCubeSet Q)
        (fun y ↦ u.toFun y - v.toH1.toFun y) := by
    exact mul_nonneg
      (mul_nonneg hlam0 (by positivity))
      (normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet Q))
  calc
    localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
        2 * (P₁ *
          (Ch02.lambdaS Q t a * (3 : ℝ) ^ (-(2 * Q.scale)) *
            normalizedL2SqOnSet (openCubeSet Q)
              (fun y ↦ u.toFun y - v.toH1.toFun y))) +
          2 * ((18 : ℝ) ^ d *
            dirichletEnergyWithRHSRHS C₂ Q a (2 * t) g v ^ 2) := by
      calc
        _ ≤ 2 * (caccioppoliWithRHSPrefactor C₁ Q a s t *
              (Ch02.lambdaS Q t a * (3 : ℝ) ^ (-(2 * Q.scale)) *
                normalizedL2SqOnSet (openCubeSet Q)
                  (fun y ↦ u.toFun y - v.toH1.toFun y))) +
            2 * ((18 : ℝ) ^ d *
              dirichletEnergyWithRHSRHS C₂ Q a (2 * t) g v ^ 2) := hraw
        _ ≤ 2 * (P₁ *
              (Ch02.lambdaS Q t a * (3 : ℝ) ^ (-(2 * Q.scale)) *
                normalizedL2SqOnSet (openCubeSet Q)
                  (fun y ↦ u.toFun y - v.toH1.toFun y))) +
            2 * ((18 : ℝ) ^ d *
              dirichletEnergyWithRHSRHS C₂ Q a (2 * t) g v ^ 2) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hprefBase hparentCarrier0) (by norm_num)) le_rfl
    _ ≤ (2 * Kp) * P₁ * B + Md * P₁ * B := add_le_add hfirst hsecond
    _ ≤ M * P₁ * B := htoM
    _ ≤ caccioppoliWithRHSPrefactor C Q a s t * B :=
      mul_le_mul_of_nonneg_right hpref hB0
    _ = caccioppoliWithRHSPrefactor C Q a s t * (BU + BF + BH) := rfl

end
end SubdiffusiveProcess.Caccioppoli
