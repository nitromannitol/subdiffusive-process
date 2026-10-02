import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCoverAssembly
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryDirectDatum
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEllipticityCaps
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.LocalControlGeometry

/-!
# Adaptive estimate on one projected boundary cell

This module performs all covariance, local-ellipticity, centering, and
physical-energy readout steps for a single cell in the fixed depth-two cover.
The remaining finite assembly sees only the explicit parent-scale budget.

PROVENANCE: this is the one-cell composition in
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryOuterAssembly.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem translatedCube_subset_anchorParent_of_nextWindow
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

/-- Every projected boundary cell satisfies the adaptive radius estimate in
the original physical coefficient field.  All good-event and local-control
hypotheses have been discharged; only the explicit local square budget is
retained for the finite-cover collapse. -/
theorem exists_projectedBoundaryCellEnergy_le_adaptiveBudget
    (d : ℕ) [NeZero d] :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (s : ℝ), s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (sOrder : FractionalOrder), sOrder.1 = s →
      ∀
        (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
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
            (∀ y, g0 y = g (y + c)) ∧
            (∀ y, u0.grad y = u.grad (y + c)) ∧
            (∀ y, h0.grad y = h.grad (y + c)) ∧
            let BE := cubeAverage Q (coefficientEnergyDensity
              (publicCoeffField Q
                (aCutoffFamily M L (translatePotentialSample c omega))) h0.grad)
            let Ag := sigma⁻¹ *
              (1 + Section6Localization.subunitCollapseConstant d *
                Section6Localization.subunitEnvelope (s / 8) (n + 2) *
                Section6Localization.subunitDeviation M (n + 2)
                  (translatePotentialSample z omega)) *
              (Fintype.card (Fin d) : ℝ) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 3) g0 ^ 2
            normalizedSetAverage
                (truncatedCube d (m : ℤ) (k - 2) q) (fun y ↦
                  SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
                    vecNormSq (u.grad y)) ≤
              ((81 : ℝ) ^ d * (18 : ℝ) ^ d) *
                (((5 / 2 : ℝ) * BE +
                    boundaryCommonGapPowerBudget Q s sigma B C BE
                      (fun y ↦ u0.toFun y - h0.toFun y)
                      (fun y ↦ -(cubeFluctuationVec Q g0 y)) +
                    (5 / 2 : ℝ) * Ag) *
                  coarseCaccioppoliRadiusIterationConst 8) := by
  obtain ⟨C, hC, hadaptive⟩ :=
    exists_boundaryCrossScaleEnergyProfile_oneThird_le_goodEventAt_centered d
  obtain ⟨E₀, B, hE₀, hB, hcaps⟩ :=
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
  obtain ⟨g0, u0, h0, hg0, hu0val, hgLocal, hu0grad, heq, hh0val,
      hh0grad, hhLocal, hgNeg, htrace⟩ :=
    exists_projectedBoundaryDirectDatum M L omega m k q sOrder u h g
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
    have hcz : c + z0 = z := by
      dsimp [z0]
      abel_nf
    rwa [hcz]
  have hanchor : translatedCube d k c ⊆
      translatedCube d ((n : ℤ) + 2) z := by
    exact translatedCube_subset_anchorParent_of_nextWindow hx
      (by simpa [k] using hPsub)
  have hQ : openCubeSet Q ⊆ translatedCube d ((n + 2 : ℕ) : ℤ) z0 := by
    intro p hp
    rw [Section6ExcessDecay.mem_translatedCube_iff]
    have hphys : p + c ∈ translatedCube d k c := by
      rw [Section6ExcessDecay.mem_translatedCube_iff]
      simpa [add_sub_cancel_right] using hp
    have hparent := hanchor hphys
    rw [Section6ExcessDecay.mem_translatedCube_iff] at hparent
    rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by norm_num]
    convert hparent using 1
    dsimp [z0]
    abel_nf
  have hg0eq : g0 = fun y ↦ g (y + c) := funext hg0
  have hgReg : ForceBesovRegularity Q (s / 3) g0 := by
    rw [hg0eq]
    exact forceBesovRegularity_of_memCubeEuclideanFullWsp_of_exponent_le
      hgLocal (by rw [hsOrder]; linarith)
  have hgNegLower : ForceBesovRegularity Q (s / 3) (fun y ↦ -g0 y) :=
    hgNeg.of_exponent_le (by rw [hsOrder]; linarith)
  have hcenteredNeg := isForcedEquation_cubeFluctuationVec hgNegLower heq
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
    abel_nf
  have heqCentered : IsForcedEquation Q (aCutoffFamily M L omega0) u0
      (fun y ↦ -(cubeFluctuationVec Q g0 y)) := by
    rw [← hfluctNeg]
    exact hcenteredNeg
  have hsGoodLower : 64 * M.delta ^ 2 ≤ s / 8 := by linarith only [hs.1]
  have hsGoodUpper : s / 8 ≤ 1 / 2 := by linarith only [hs.2]
  have hsigmaEq : tailAverage M L (n + 2) omega0
      (translatedCube d ((n + 2 : ℕ) : ℤ) z0) = sigma := by
    rw [Section6Covariance.tailAverage_translatePotentialSample_translatedCube]
    rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by norm_num]
    congr 1
    dsimp [z0]
    abel_nf
  have hsampleEq : translatePotentialSample z0 omega0 =
      translatePotentialSample z omega := by
    dsimp [omega0]
    rw [Section6Covariance.translatePotentialSample_translate]
    congr 1
    dsimp [z0]
    abel_nf
  have hupper : (tailAverage M L (n + 2) omega0
        (translatedCube d ((n + 2 : ℕ) : ℤ) z0))⁻¹ *
      Ch02.LambdaSq Q (s / 6) (.finite 2) (aCutoffFamily M L omega0) ≤ B := by
    rw [hsigmaEq]
    exact hcap.2.1
  have hlower : tailAverage M L (n + 2) omega0
        (translatedCube d ((n + 2 : ℕ) : ℤ) z0) *
      (Ch02.lambdaSq Q (s / 6) (.finite 2) (aCutoffFamily M L omega0))⁻¹ ≤ B := by
    rw [hsigmaEq]
    exact hcap.2.2.1
  have hcenteredReg : ForceBesovRegularity Q (s / 3)
      (fun y ↦ -(cubeFluctuationVec Q g0 y)) := by
    have hreg := forceBesovRegularity_cubeFluctuationVec hgNegLower
    rw [hfluctNeg] at hreg
    exact hreg
  have hprofile := hadaptive M omega0 z0 Q (q - c) g0 u0 h0
    hnL hgood0 hsGoodLower hsGoodUpper hQ heqCentered htrace hs0 hs.2 hB
    hupper hlower hgReg hcenteredReg
  have hread := normalizedCutoffEnergy_truncatedCube_le_profile
    M L omega hqDomain hkm u u0 hu0grad
  refine ⟨g0, u0, h0, hg0, hu0grad, hh0grad, ?_⟩
  dsimp only
  have hmul := mul_le_mul_of_nonneg_left hprofile
    (by positivity : (0 : ℝ) ≤ (81 : ℝ) ^ d * (18 : ℝ) ^ d)
  refine hread.trans ?_
  rw [hsigmaEq, hsampleEq] at hmul
  simpa only [k, c, Q, omega0, sigma, mul_assoc] using hmul

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
