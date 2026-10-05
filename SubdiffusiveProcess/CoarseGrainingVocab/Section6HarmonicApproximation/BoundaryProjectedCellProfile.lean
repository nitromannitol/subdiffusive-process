module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAffineResidual
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEllipticityCaps
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryPhysicalCarrierGoodEventPrices
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryPhysicalCarrierAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryProfileReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryRegularity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.LocalControlGeometry

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem translatedCube_subset_anchorParent_of_nextWindow_profile
    {m n : ℤ} {x y z : Vec d}
    (hx : x ∈ truncatedCube d m (n - 3) z)
    (hD : translatedCube d (n - 2) y ⊆ truncatedCube d m n x) :
    translatedCube d (n - 2) y ⊆ translatedCube d (n + 2) z := by
  intro p hp
  have hpx : p - x ∈ cube d n :=
    Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube (hD hp)
  have hxz : x - z ∈ cube d (n - 3) :=
    Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube hx
  rw [cube, mem_openCubeSet_originCube_iff] at hpx hxz
  rw [Section6ExcessDecay.mem_translatedCube_iff, cube,
    mem_openCubeSet_originCube_iff]
  intro i
  have hbase : (0 : ℝ) < (3 : ℝ) ^ (n - 3) := zpow_pos (by norm_num) _
  have h1 : (3 : ℝ) ^ n = 27 * (3 : ℝ) ^ (n - 3) := by
    rw [show n = (n - 3) + 3 by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have h2 : (3 : ℝ) ^ (n + 2) = 243 * (3 : ℝ) ^ (n - 3) := by
    rw [show n + 2 = (n - 3) + 5 by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have hid : p i - z i = (p i - x i) + (x i - z i) := by ring
  simp only [Pi.sub_apply] at hpx hxz ⊢
  rw [h1] at hpx
  rw [hid, h2]
  constructor <;>
    linarith only [(hpx i).1, (hpx i).2, (hxz i).1, (hxz i).2, hbase]

/-- On a projected boundary cell, the physical-carrier endpoint may be run
with the same-boundary Dirichlet comparison as its datum. -/
theorem exists_projectedBoundaryCellPhysicalProfile (d : ℕ) [NeZero d] :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (s : ℝ), s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (sOrder : FractionalOrder), sOrder.1 = s →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x q : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        MemFractionalOn (cube d (m : ℤ)) s h.grad →
        let k : ℤ := (n : ℤ) - 2
        let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
        let Q := originCube d k
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        ∃ g0 : Vec d → Vec d,
          ∃ u0 h0 : H1Function (openCubeSet Q),
          ∃ v : DirichletForcedCubeSolution Q
              (aCutoffFamily M L (translatePotentialSample c omega))
              (fun y ↦ -g0 y),
            (∀ y, g0 y = g (y + c)) ∧
            (∀ y, u0.toFun y = u.toFun (y + c)) ∧
            Ch03.ABK26.MemCubeEuclideanFullWsp Q sOrder
              FiniteLpExponent.two (fun y ↦ g (y + c)) ∧
            (∀ y, u0.grad y = u.grad (y + c)) ∧
            IsForcedEquation Q
              (aCutoffFamily M L (translatePotentialSample c omega)) u0
              (fun y ↦ -(cubeFluctuationVec Q g0 y)) ∧
            v.boundaryData = h0 ∧
            (∀ y, h0.toFun y = h.toFun (y + c)) ∧
            (∀ y, h0.grad y = h.grad (y + c)) ∧
            Ch03.ABK26.MemCubeEuclideanFullWsp Q sOrder
              FiniteLpExponent.two (fun y ↦ h.grad (y + c)) ∧
            ForceBesovRegularity Q sOrder.1 (fun y ↦ -g0 y) ∧
            ForceBesovRegularity Q sOrder.1 (dirichletBoundaryGradientField v) ∧
            let BE := cubeAverage Q (coefficientEnergyDensity
              (publicCoeffField Q
                (aCutoffFamily M L (translatePotentialSample c omega)))
              v.toH1.grad)
            let Ag := sigma⁻¹ *
              (1 + Section6Localization.subunitCollapseConstant d *
                Section6Localization.subunitEnvelope (s / 8) (n + 2) *
                Section6Localization.subunitDeviation M (n + 2)
                  (translatePotentialSample z omega)) *
              (Fintype.card (Fin d) : ℝ) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 3) g0 ^ 2
            boundaryCrossScaleEnergyProfile Q Q (q - c) (1 / 3 : ℝ)
                (fun y ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L
                  (translatePotentialSample c omega) y * vecNormSq (u0.grad y)) ≤
              ((57 / 8 : ℝ) * BE +
                4 * (1 / 8 + (64 * C ^ 4 * B)⁻¹) * BE +
                3 * Ag +
                4 * boundaryCommonGapPowerBudget Q s sigma B C 0
                  (fun y ↦ u0.toFun y - v.toH1.toFun y)
                  (fun y ↦ -(cubeFluctuationVec Q g0 y))) *
                boundaryThreeQuarterRadiusIterationConst := by
  obtain ⟨C, hC, hprofile⟩ :=
    exists_boundaryCrossScaleEnergyProfile_oneThird_le_goodEventAt_physicalCarrier d
  obtain ⟨_E, B, _hE, hB, hcaps⟩ :=
    exists_localBoundaryEllipticityCaps_nextWindow d
  refine ⟨C, B, hC, hB, ?_⟩
  intro M s hs sOrder hsOrder L m n hmL hnm z x q omega hx hq hgood u h g
    hdir hg hhfrac
  let k : ℤ := (n : ℤ) - 2
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q : TriadicCube d := originCube d k
  let omega0 := translatePotentialSample c omega
  let z0 : Vec d := z - c
  let sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hkm : k ≤ (m : ℤ) := by dsimp [k]; omega
  have hnL : n + 2 ≤ L := by omega
  have hqDomain : q ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 1) x hq
  have hhFull : Ch03.ABK26.MemCubeEuclideanFullWsp
      (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad := by
    apply memCubeEuclideanFullWsp_grad_of_memFractionalOn
    simpa [cube, hsOrder] using hhfrac
  obtain ⟨g0, u0, h0, v, hg0, hu0val, hgLocal, hu0grad, heq, hv,
      hh0val, hh0grad, hhLocal, htrace, hgReg, hhReg⟩ :=
    exists_projectedBoundaryDatum_regular M L omega m k q sOrder u h g
      hdir hg hhFull hkm
  have hPsub : translatedCube d k c ⊆
      truncatedCube d (m : ℤ) (n : ℤ) x := by
    exact translatedCube_wellPlacedCentre_subset_nextWindow_of_mem
      (by simpa [k] using hq) hkm
  have hcP : c ∈ translatedCube d k c := by
    rw [Section6ExcessDecay.mem_translatedCube_iff]
    simpa using Section6ExcessDecay.zero_mem_cube d k
  have hcU : c ∈ truncatedCube d (m : ℤ) (n : ℤ) x := hPsub hcP
  have hcap := hcaps M s hs L m n hnL z x c omega hx hcU hgood
  have hgood0 : omega0 ∈ goodEvent M none (n + 2) z0 1 (s / 8) := by
    apply (Section6Covariance.mem_goodEvent_translatePotentialSample
      M none (n + 2) z0 1 (s / 8) c omega).2
    have hcz : c + z0 = z := by dsimp [z0]; abel_nf
    rwa [hcz]
  have hanchor : translatedCube d k c ⊆
      translatedCube d ((n : ℤ) + 2) z := by
    exact translatedCube_subset_anchorParent_of_nextWindow_profile hx
      (by simpa [k] using hPsub)
  have hQ : openCubeSet Q ⊆ translatedCube d ((n + 2 : ℕ) : ℤ) z0 := by
    intro p hp
    rw [Section6ExcessDecay.mem_translatedCube_iff]
    have hphys : p + c ∈ translatedCube d k c := by
      rw [Section6ExcessDecay.mem_translatedCube_iff]
      simpa [add_sub_cancel_right] using! hp
    have hparent := hanchor hphys
    rw [Section6ExcessDecay.mem_translatedCube_iff] at hparent
    rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by norm_num]
    convert hparent using 1
    dsimp [z0]
    abel_nf
  have hg0eq : g0 = fun y ↦ g (y + c) := funext hg0
  have hgRegLower : ForceBesovRegularity Q (s / 3) g0 := by
    rw [hg0eq]
    exact forceBesovRegularity_of_memCubeEuclideanFullWsp_of_exponent_le
      hgLocal (by rw [hsOrder]; linarith)
  have hgNegLower : ForceBesovRegularity Q (s / 3) (fun y ↦ -g0 y) :=
    hgReg.of_exponent_le (by rw [hsOrder]; linarith)
  have hcentered := isForcedEquation_cubeFluctuationVec hgNegLower heq
  have hzero : MemLp (0 : Vec d → Vec d) 2 (normalizedCubeMeasure Q) := by simp
  have hg0Lp : MemLp g0 2 (normalizedCubeMeasure Q) := by
    rw [hg0eq]
    exact Ch03.ABK26.MemCubeEuclideanFullWsp.memLpTwo (by norm_num) hgLocal
  have havgNeg : cubeAverageVec Q (fun y ↦ -g0 y) = -cubeAverageVec Q g0 := by
    have hzeroavg : cubeAverageVec Q (0 : Vec d → Vec d) = 0 := by
      funext i
      simp [cubeAverageVec, cubeAverage]
    simpa [hzeroavg] using
      cubeAverageVec_sub_memLp Q (0 : Vec d → Vec d) g0 hzero hg0Lp
  have hfluctNeg : cubeFluctuationVec Q (fun y ↦ -g0 y) =
      fun y ↦ -(cubeFluctuationVec Q g0 y) := by
    funext y
    rw [cubeFluctuationVec_apply, cubeFluctuationVec_apply, havgNeg]
    abel
  have heqCentered : IsForcedEquation Q (aCutoffFamily M L omega0) u0
      (fun y ↦ -(cubeFluctuationVec Q g0 y)) := by
    rw [← hfluctNeg]
    exact hcentered
  have hsGoodLower : 64 * M.delta ^ 2 ≤ s / 8 := by linarith only [hs.1]
  have hsGoodUpper : s / 8 ≤ 1 / 2 := by linarith only [hs.2]
  have hsigmaEq : tailAverage M L (n + 2) omega0
      (translatedCube d ((n + 2 : ℕ) : ℤ) z0) = sigma := by
    rw [Section6Covariance.tailAverage_translatePotentialSample_translatedCube]
    rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by norm_num]
    congr 1
    dsimp [z0]
    abel_nf
  have hsigma : 0 < tailAverage M L (n + 2) omega0
      (translatedCube d ((n + 2 : ℕ) : ℤ) z0) := by
    rw [hsigmaEq]
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hupper : (tailAverage M L (n + 2) omega0
        (translatedCube d ((n + 2 : ℕ) : ℤ) z0))⁻¹ *
      Ch02.LambdaSq Q (s / 6) (.finite 2) (aCutoffFamily M L omega0) ≤ B := by
    rw [hsigmaEq]
    exact hcap.2.1
  have hlower : tailAverage M L (n + 2) omega0
        (translatedCube d ((n + 2 : ℕ) : ℤ) z0) *
      (Ch02.lambdaSq Q (s / 6) (.finite 2)
        (aCutoffFamily M L omega0))⁻¹ ≤ B := by
    rw [hsigmaEq]
    exact hcap.2.2.1
  have hcenteredReg : ForceBesovRegularity Q (s / 3)
      (fun y ↦ -(cubeFluctuationVec Q g0 y)) := by
    have hreg := forceBesovRegularity_cubeFluctuationVec hgNegLower
    rw [hfluctNeg] at hreg
    exact hreg
  let ell : H1Function (openCubeSet Q) :=
    H1Function.affineOnIsSobolevRegularDomain
      (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain (0 : Vec d)
  obtain ⟨vzero, hvzero, htraceZero, henergyZero⟩ :=
    exists_pointwiseAffineDirichletRepresentative M L omega0 Q
      (by positivity : 0 < s / 6) hsigma hupper (0 : Vec d)
  have hvzeroEnergy : localizedCoeffEnergyValue (openCubeSet Q)
      ((aCutoffFamily M L omega0).coeffOn Q) vzero ≤ 0 := by
    have hz : vecNormSq (0 : Vec d) = 0 := by simp [vecNormSq, vecDot]
    simpa only [hz, mul_zero] using henergyZero
  have hellEnergy : localizedCoeffEnergyValue (openCubeSet Q)
      ((aCutoffFamily M L omega0).coeffOn Q) ell ≤ 0 := by
    have hzero : localizedCoeffEnergyValue (openCubeSet Q)
        ((aCutoffFamily M L omega0).coeffOn Q) ell = 0 := by
      rw [localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
        (Set.Subset.rfl) ell]
      unfold coefficientEnergyDensity volumeAverage
      simp [ell, H1Function.affineOnIsSobolevRegularDomain_grad, vecDot]
    exact hzero.le
  have hprofileRaw := hprofile M omega0 z0 Q (q - c) g0 u0 v.toH1 vzero ell
    hnL hgood0 hsGoodLower hsGoodUpper hQ heqCentered hvzero htrace htraceZero
      hvzeroEnergy hellEnergy (by norm_num) (by norm_num) hs0 hs.2 hB hupper
      hlower hgRegLower hcenteredReg
  refine ⟨g0, u0, h0, v, hg0, hu0val, hgLocal, hu0grad, heqCentered, hv, hh0val,
    hh0grad, hhLocal, hgReg, hhReg, ?_⟩
  have hz0 : c + z0 = z := by
    dsimp only [z0]
    abel
  dsimp only at hprofileRaw ⊢
  rw [hsigmaEq] at hprofileRaw
  have hgapFun {U : Set (Vec d)} (u v : H1Function U) :
      (u - v).toFun = fun y ↦ u.toFun y - v.toFun y := by
    simpa only using! (H1Function.sub_toFun u v)
  dsimp only [Q, Ch02.cubeDomain] at hprofileRaw
  set_option backward.isDefEq.respectTransparency false in
    rw [hgapFun] at hprofileRaw
  simpa only [k, c, Q, omega0, sigma, H1Function.sub_toFun, Pi.sub_apply,
    Section6Covariance.translatePotentialSample_translate, sub_add_cancel,
    hz0, mul_zero, zero_add, add_zero] using! hprofileRaw

/-- The preceding projected comparison profile read back on the literal
physical child.  Its three analytic prices are exposed only through the
`BE`, `Ag`, and common-gap comparisons used by the final budget collapse. -/
theorem exists_projectedBoundaryCellPhysicalEnergy_of_budgetCaps
    (d : ℕ) [NeZero d] :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (s : ℝ), s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (sOrder : FractionalOrder), sOrder.1 = s →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x q : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        MemFractionalOn (cube d (m : ℤ)) s h.grad →
        let k : ℤ := (n : ℤ) - 2
        let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
        let Q := originCube d k
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        ∃ g0 : Vec d → Vec d,
          ∃ u0 h0 : H1Function (openCubeSet Q),
          ∃ v : DirichletForcedCubeSolution Q
              (aCutoffFamily M L (translatePotentialSample c omega))
              (fun y ↦ -g0 y),
            (∀ y, g0 y = g (y + c)) ∧
            Ch03.ABK26.MemCubeEuclideanFullWsp Q sOrder
              FiniteLpExponent.two (fun y ↦ g (y + c)) ∧
            (∀ y, u0.grad y = u.grad (y + c)) ∧
            IsForcedEquation Q
              (aCutoffFamily M L (translatePotentialSample c omega)) u0
              (fun y ↦ -(cubeFluctuationVec Q g0 y)) ∧
            v.boundaryData = h0 ∧
            (∀ y, h0.grad y = h.grad (y + c)) ∧
            ∀ H G P : ℝ,
              cubeAverage Q (coefficientEnergyDensity
                  (publicCoeffField Q
                    (aCutoffFamily M L (translatePotentialSample c omega)))
                  v.toH1.grad) ≤ H →
              sigma⁻¹ *
                    (1 + Section6Localization.subunitCollapseConstant d *
                      Section6Localization.subunitEnvelope (s / 8) (n + 2) *
                      Section6Localization.subunitDeviation M (n + 2)
                        (translatePotentialSample z omega)) *
                    (Fintype.card (Fin d) : ℝ) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 3) g0 ^ 2 ≤ G →
              boundaryCommonGapPowerBudget Q s sigma B C 0
                  (fun y ↦ u0.toFun y - v.toH1.toFun y)
                  (fun y ↦ -(cubeFluctuationVec Q g0 y)) ≤ P →
              normalizedSetAverage
                  (truncatedCube d (m : ℤ) (k - 2) q) (fun y ↦
                    _root_.SubdiffusiveProcess.Model.aCutoff M L omega y *
                      vecNormSq (u.grad y)) ≤
                ((81 : ℝ) ^ d * (18 : ℝ) ^ d) *
                  (((61 / 8 : ℝ) + 4 * (64 * C ^ 4 * B)⁻¹) * H +
                      3 * G + 4 * P) *
                    boundaryThreeQuarterRadiusIterationConst := by
  obtain ⟨C, B, hC, hB, hprofile⟩ :=
    exists_projectedBoundaryCellPhysicalProfile d
  refine ⟨C, B, hC, hB, ?_⟩
  intro M s hs sOrder hsOrder L m n hmL hnm z x q omega hx hq hgood
    u h g hdir hg hh
  obtain ⟨g0, u0, h0, v, hg0, _hu0val, hgLocal, hu0, heq, hv, _hh0val,
      hh0, _hhLocal, _hgReg, _hhReg, hraw⟩ :=
    hprofile M s hs sOrder hsOrder L m n hmL hnm z x q omega hx hq hgood
      u h g hdir hg hh
  let k : ℤ := (n : ℤ) - 2
  let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q := originCube d k
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  refine ⟨g0, u0, h0, v, hg0, hgLocal, hu0, heq, hv, hh0, ?_⟩
  intro H G P hBE hAg hX
  have hqDomain : q ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 1) x hq
  have hkm : k ≤ (m : ℤ) := by dsimp [k]; omega
  have hread := normalizedCutoffEnergy_truncatedCube_le_profile
    M L omega hqDomain hkm u u0 hu0
  let BE := cubeAverage Q (coefficientEnergyDensity
    (publicCoeffField Q (aCutoffFamily M L (translatePotentialSample c omega)))
    v.toH1.grad)
  let Ag := sigma⁻¹ *
    (1 + Section6Localization.subunitCollapseConstant d *
      Section6Localization.subunitEnvelope (s / 8) (n + 2) *
      Section6Localization.subunitDeviation M (n + 2)
        (translatePotentialSample z omega)) *
    (Fintype.card (Fin d) : ℝ) *
    scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 3) g0 ^ 2
  let X := boundaryCommonGapPowerBudget Q s sigma B C 0
    (fun y ↦ u0.toFun y - v.toH1.toFun y)
    (fun y ↦ -(cubeFluctuationVec Q g0 y))
  let E := boundaryCrossScaleEnergyProfile Q Q (q - c) (1 / 3 : ℝ)
    (fun y ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L
      (translatePotentialSample c omega) y * vecNormSq (u0.grad y))
  have hrawExpanded : E ≤
      ((79 / 8 : ℝ) * 0 + (57 / 8 : ℝ) * BE +
          4 * (1 / 8 + (64 * C ^ 4 * B)⁻¹) * BE + 13 * 0 +
          3 * Ag + 4 * X) * boundaryThreeQuarterRadiusIterationConst := by
    dsimp only [E, BE, Ag, X, k, c, Q, sigma]
    simpa only [mul_zero, zero_add, add_zero] using hraw
  have hcollected := boundaryPhysicalCarrier_profile_le_fourBudgets_of_raw
    hC hB hrawExpanded (Av := 0) (Aell := 0) (BE := BE) (Ag := Ag)
      (X := X) (E := E) (A := 0) (H := H) (G := G) (P := P)
      (by norm_num) (by norm_num) hBE hAg hX
  have hmul := mul_le_mul_of_nonneg_left hcollected
    (by positivity : (0 : ℝ) ≤ (81 : ℝ) ^ d * (18 : ℝ) ^ d)
  refine hread.trans ?_
  dsimp only at hmul ⊢
  simpa only [k, c, Q, sigma, mul_zero, zero_add, mul_assoc] using hmul

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
