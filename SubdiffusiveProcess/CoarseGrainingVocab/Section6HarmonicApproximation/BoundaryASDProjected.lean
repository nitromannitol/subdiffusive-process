module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryASDSeparateDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryDirectDatum

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

private noncomputable def projectedWspField
    {Q : TriadicCube d} {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    CubeEuclideanWspField Q s FiniteLpExponent.two where
  toField := f
  euclideanMemLp := hf.1
  euclideanMemWsp := hf.2

omit [NeZero d] in
@[simp] private theorem projectedWspField_toField
    {Q : TriadicCube d} {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    (projectedWspField hf).toField = f := rfl

private theorem forceBesovRegularity_of_projectedFull
    {Q : TriadicCube d} {s : FractionalOrder} {f : Vec d → Vec d}
    (hf : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two f) :
    ForceBesovRegularity Q s.1 f := by
  have hSob := cubeEuclideanWspField_forceSobolevRegularity s
    (projectedWspField hf)
  simpa using hSob.toForceBesovRegularity s.2.1 s.2.2.le

/-- The source-exact ASD row on one well-placed projected boundary cube.

The scalar in the parent is the cube mean of the transported physical datum,
which is exactly the normalization required by the source lemma. -/
theorem exists_projectedBoundaryCellASD (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        (m : ℕ) (k : ℤ) (q : Vec d) (sOrder : FractionalOrder)
        (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad →
        sOrder.1 ≤ 1 / 4 → k ≤ (m : ℤ) → q ∈ cube d (m : ℤ) →
        let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
        let Q := originCube d k
        let A := aCutoffFamily M L (translatePotentialSample c omega)
        ∃ g0 : Vec d → Vec d,
          ∃ u0 h0 : H1Function (openCubeSet Q),
            (∀ x, g0 x = g (x + c)) ∧
            (∀ x, u0.toFun x = u.toFun (x + c)) ∧
            (∀ x, u0.grad x = u.grad (x + c)) ∧
            (∀ x, h0.toFun x = h.toFun (x + c)) ∧
            (∀ x, h0.grad x = h.grad (x + c)) ∧
            localizedCoeffEnergyValue
                (caccioppoliCoreSet Q (q - c)) (A.coeffOn Q) u0 ≤
              caccioppoliWithRHSPrefactor C Q A (1 / 2) (sOrder.1 / 2) *
                (Ch02.lambdaS Q (sOrder.1 / 2) A *
                    Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                    normalizedL2SqOnSet (openCubeSet Q) (fun y ↦
                      u0.toFun y - volumeAverage (openCubeSet Q) h0.toFun) +
                  Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
                    Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
                      (fun x ↦ -g0 x) ^ 2 +
                  Real.rpow (sOrder.1 / 2) (-3 : ℝ) *
                    Ch02.LambdaS Q (sOrder.1 / 2) A *
                    scaleNormalizedPositiveBesovVectorNormTwo Q sOrder.1 h0.grad ^ 2) := by
  obtain ⟨C, hC, hASD⟩ := exists_boundary_caccioppoli_quarter_with_datum d
  refine ⟨C, hC, ?_⟩
  intro M L omega m k q sOrder u h g hdir hg hh hs4 hkm hq
  dsimp only
  obtain ⟨g0, u0, h0, hg0, hu0, hgLocal, hu0grad, huEq, hh0, hh0grad,
      hhLocal, hgReg, htrace⟩ :=
    exists_projectedBoundaryDirectDatum M L omega m k q sOrder u h g
      hdir hg hh hkm
  let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q := originCube d k
  let A := aCutoffFamily M L (translatePotentialSample c omega)
  have hhReg0 : ForceBesovRegularity Q sOrder.1
      (fun x ↦ h.grad (x + c)) :=
    forceBesovRegularity_of_projectedFull hhLocal
  have hhReg : ForceBesovRegularity Q sOrder.1 h0.grad := by
    have heq : h0.grad = fun x ↦ h.grad (x + c) := funext hh0grad
    rw [heq]
    exact hhReg0
  have hqtrunc : q ∈ truncatedCube d (m : ℤ) (k - 1) q :=
    Section6ExcessDecay.mem_truncatedCube_self (k - 1) hq
  have hqtranslated : q ∈ translatedCube d k c :=
    Section6ExcessDecay.truncatedCube_subset_translatedCube_wellPlacedCentre q
      hkm (by omega) hqtrunc
  have hx : q - c ∈ openCubeSet Q :=
    Section6ExcessDecay.mem_translatedCube_iff.mp hqtranslated
  have ht : 0 < sOrder.1 / 2 := div_pos sOrder.2.1 (by norm_num)
  have ht4 : sOrder.1 / 2 ≤ (1 : ℝ) / 4 := by linarith only [hs4]
  have hst : (1 / 2 : ℝ) + sOrder.1 / 2 < 1 := by
    linarith only [sOrder.2.2]
  have hgReg' : ForceBesovRegularity Q (2 * (sOrder.1 / 2))
      (fun x ↦ -g0 x) := by
    simpa only [show 2 * (sOrder.1 / 2) = sOrder.1 by ring] using hgReg
  have hhReg' : ForceBesovRegularity Q (2 * (sOrder.1 / 2)) h0.grad := by
    simpa only [show 2 * (sOrder.1 / 2) = sOrder.1 by ring] using hhReg
  have hbound := hASD u0 h0 (volumeAverage (openCubeSet Q) h0.toFun)
    huEq htrace rfl (by norm_num) (by norm_num) ht ht4 hst hx hgReg' hhReg'
  refine ⟨g0, u0, h0, hg0, hu0, hu0grad, hh0, hh0grad, ?_⟩
  simpa only [c, Q, A, show 2 * (sOrder.1 / 2) = sOrder.1 by ring] using hbound

/-- The projected separate-datum row at the manuscript's boundary pricing
slot `(s_c,t)=(1/2,s/3)`.  Unlike the half-order convenience endpoint above,
this form aligns directly with `caccioppoliWithRHSPrefactor_boundaryPair_le`.
-/
theorem exists_projectedBoundaryCellASD_third (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        (m : ℕ) (k : ℤ) (q : Vec d) (sOrder : FractionalOrder)
        (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad →
        sOrder.1 ≤ 1 / 4 → k ≤ (m : ℤ) → q ∈ cube d (m : ℤ) →
        let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
        let Q := originCube d k
        let A := aCutoffFamily M L (translatePotentialSample c omega)
        ∃ g0 : Vec d → Vec d,
          ∃ u0 h0 : H1Function (openCubeSet Q),
            (∀ x, g0 x = g (x + c)) ∧
            (∀ x, u0.toFun x = u.toFun (x + c)) ∧
            (∀ x, u0.grad x = u.grad (x + c)) ∧
            (∀ x, h0.toFun x = h.toFun (x + c)) ∧
            (∀ x, h0.grad x = h.grad (x + c)) ∧
            localizedCoeffEnergyValue
                (caccioppoliCoreSet Q (q - c)) (A.coeffOn Q) u0 ≤
              caccioppoliWithRHSPrefactor C Q A (1 / 2) (sOrder.1 / 3) *
                (Ch02.lambdaS Q (sOrder.1 / 3) A *
                    Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                    normalizedL2SqOnSet (openCubeSet Q) (fun y ↦
                      u0.toFun y - volumeAverage (openCubeSet Q) h0.toFun) +
                  Real.rpow (sOrder.1 / 3) (-11 : ℝ) *
                    Real.rpow (Ch02.lambdaS Q (sOrder.1 / 3) A) (-1 : ℝ) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo Q
                      (2 * (sOrder.1 / 3)) (fun x ↦ -g0 x) ^ 2 +
                  Real.rpow (sOrder.1 / 3) (-3 : ℝ) *
                    Ch02.LambdaS Q (sOrder.1 / 3) A *
                    scaleNormalizedPositiveBesovVectorNormTwo Q
                      (2 * (sOrder.1 / 3)) h0.grad ^ 2) := by
  obtain ⟨C, hC, hASD⟩ := exists_boundary_caccioppoli_quarter_with_datum d
  refine ⟨C, hC, ?_⟩
  intro M L omega m k q sOrder u h g hdir hg hh hs4 hkm hq
  dsimp only
  obtain ⟨g0, u0, h0, hg0, hu0, _hgLocal, hu0grad, huEq, hh0, hh0grad,
      hhLocal, hgReg, htrace⟩ :=
    exists_projectedBoundaryDirectDatum M L omega m k q sOrder u h g
      hdir hg hh hkm
  let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q := originCube d k
  let A := aCutoffFamily M L (translatePotentialSample c omega)
  have hhReg0 : ForceBesovRegularity Q sOrder.1
      (fun x ↦ h.grad (x + c)) :=
    forceBesovRegularity_of_projectedFull hhLocal
  have hhReg : ForceBesovRegularity Q sOrder.1 h0.grad := by
    have heq : h0.grad = fun x ↦ h.grad (x + c) := funext hh0grad
    rw [heq]
    exact hhReg0
  have hqtrunc : q ∈ truncatedCube d (m : ℤ) (k - 1) q :=
    Section6ExcessDecay.mem_truncatedCube_self (k - 1) hq
  have hqtranslated : q ∈ translatedCube d k c :=
    Section6ExcessDecay.truncatedCube_subset_translatedCube_wellPlacedCentre q
      hkm (by omega) hqtrunc
  have hx : q - c ∈ openCubeSet Q :=
    Section6ExcessDecay.mem_translatedCube_iff.mp hqtranslated
  have ht : 0 < sOrder.1 / 3 := div_pos sOrder.2.1 (by norm_num)
  have ht4 : sOrder.1 / 3 ≤ (1 : ℝ) / 4 := by linarith only [hs4]
  have hst : (1 / 2 : ℝ) + sOrder.1 / 3 < 1 := by
    linarith only [sOrder.2.2]
  have htwoThird : 2 * (sOrder.1 / 3) ≤ sOrder.1 := by
    linarith only [sOrder.2.1]
  have hgReg' : ForceBesovRegularity Q (2 * (sOrder.1 / 3))
      (fun x ↦ -g0 x) := hgReg.of_exponent_le htwoThird
  have hhReg' : ForceBesovRegularity Q (2 * (sOrder.1 / 3)) h0.grad :=
    hhReg.of_exponent_le htwoThird
  have hbound := hASD u0 h0 (volumeAverage (openCubeSet Q) h0.toFun)
    huEq htrace rfl (by norm_num) (by norm_num) ht ht4 hst hx hgReg' hhReg'
  exact ⟨g0, u0, h0, hg0, hu0, hu0grad, hh0, hh0grad, hbound⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
