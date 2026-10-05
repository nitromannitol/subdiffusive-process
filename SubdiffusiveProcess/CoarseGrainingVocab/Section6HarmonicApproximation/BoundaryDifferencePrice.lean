module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.NegativeNormToL2
public import Homogenization.Book.Ch03.Theorems.CoarsePoincareRHS
public import Homogenization.Book.Ch03.Theorems.EnergyRHS.Theory

@[expose] public section

/-!
# Pricing the structural Dirichlet datum difference

The boundary Caccioppoli term contains `v-h_tilde`, where `v` is a public
`DirichletForcedCubeSolution`.  Its structural zero-trace witness is first
priced by the negative-norm-to-`L2` estimate and then split into the solution
gradient and boundary gradient.  The solution gradient is handled by the
finite-`2` forced coarse-Poincare theorem.

follows the decomposition.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Local Euclidean normalized `L²` carrier used to price the boundary
gradient.  This is kept internal to the harmonic-approximation decomposition. -/
noncomputable def boundaryNormalizedEuclideanL2 (Q : TriadicCube d)
    (F : Vec d → Vec d) : ℝ :=
  cubeLpNorm Q (2 : ℝ≥0∞) fun x => HilbertVec.ofVec (F x)

theorem boundaryNormalizedEuclideanL2_nonneg (Q : TriadicCube d)
    (F : Vec d → Vec d) : 0 ≤ boundaryNormalizedEuclideanL2 Q F :=
  cubeLpNorm_nonneg Q (2 : ℝ≥0∞) _

private theorem memVectorL2_cubeSet_of_openCubeSet {Q : TriadicCube d}
    {F : Vec d → Vec d} (h : MemVectorL2 (openCubeSet Q) F) :
    MemVectorL2 (cubeSet Q) F := by
  rw [MemVectorL2, volumeMeasureOn,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
  exact h

private theorem memLp_hilbert_normalizedCubeMeasure {Q : TriadicCube d}
    {F : Vec d → Vec d} (hF : MemVectorL2 (cubeSet Q) F) :
    MemLp (fun x => HilbertVec.ofVec (F x)) 2 (normalizedCubeMeasure Q) := by
  have hHilbert : MemLp (fun x => HilbertVec.ofVec (F x)) 2
      (volumeMeasureOn (cubeSet Q)) := memHilbertVectorL2_hilbertifyVecField hF
  simpa only [volumeMeasureOn, normalizedCubeMeasure, cubeMeasure] using
    hHilbert.smul_measure ENNReal.ofReal_ne_top

private theorem boundaryNormalizedEuclideanL2_sq {Q : TriadicCube d}
    {F : Vec d → Vec d} (hF : MemVectorL2 (cubeSet Q) F) :
    boundaryNormalizedEuclideanL2 Q F ^ (2 : ℕ) =
      cubeAverage Q fun x => vecNormSq (F x) := by
  have hmem := memLp_hilbert_normalizedCubeMeasure hF
  have hbase := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
    (Q := Q) (p := (2 : ℝ≥0∞)) (f := fun x => HilbertVec.ofVec (F x))
    (by norm_num) (by norm_num) hmem
  rw [show ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) by norm_num] at hbase
  simp only [Real.rpow_natCast] at hbase
  rw [boundaryNormalizedEuclideanL2, hbase]
  refine congrArg (cubeAverage Q) ?_
  funext x
  rw [HilbertVec.norm_sq_ofVec]
  rfl

/-- Dimension-only price of the negative-norm triangle step. -/
noncomputable def boundaryDifferencePriceConst (d : ℕ) [NeZero d] : ℝ :=
  negativeNormToL2Constant d * Real.sqrt 2

theorem boundaryDifferencePriceConst_pos (d : ℕ) [NeZero d] :
    0 < boundaryDifferencePriceConst d := by
  exact mul_pos (negativeNormToL2Constant_pos d) (Real.sqrt_pos.2 (by norm_num))

/-- The datum difference is bounded by the two negative Besov gradient
seminorms. -/
theorem cubeBesovScaleWeight_mul_cubeLpNorm_datumDifference_le_negativeBesov
    [NeZero d] (Q : TriadicCube d) {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (hs : 0 < s) (hs1 : s ≤ 1) :
    cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - v.boundaryData.toFun y) ≤
      boundaryDifferencePriceConst d *
        (cubeBesovNegativeVectorSeminormTwo Q (s / 2) (fun x => v.toH1.grad x) +
          cubeBesovNegativeVectorSeminormTwo Q (s / 2)
            (fun x => v.boundaryData.grad x)) := by
  classical
  let w := v.zeroTraceDifferenceH10CubeSet
  have hvL2 : MemVectorL2 (cubeSet Q) (fun x => v.toH1.grad x) :=
    memVectorL2_cubeSet_of_openCubeSet v.toH1.grad_memVectorL2
  have hhL2 : MemVectorL2 (cubeSet Q) (fun x => v.boundaryData.grad x) :=
    memVectorL2_cubeSet_of_openCubeSet v.boundaryData.grad_memVectorL2
  have hvLp : MemLp (fun x => v.toH1.grad x) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hvL2
  have hhLp : MemLp (fun x => v.boundaryData.grad x) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hhL2
  have hvBdd := cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q
    (by linarith only [hs] : 0 < s / 2) (fun x => v.toH1.grad x) hvLp
  have hhBdd := cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q
    (by linarith only [hs] : 0 < s / 2) (fun x => v.boundaryData.grad x) hhLp
  have hval := cubeLpNorm_h10_le_negativeBesov_half Q w hs hs1
  have hwval : w.toH1Function.toFun
      =ᵐ[volume.restrict (cubeSet Q)]
        (fun y => v.toH1.toFun y - v.boundaryData.toFun y) := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    simpa [w] using v.zeroTraceDifferenceH10_toFun_ae_eq
  have hLHS : cubeLpNorm Q (2 : ℝ≥0∞) (fun y => w.toH1Function.toFun y) =
      cubeLpNorm Q (2 : ℝ≥0∞)
        (fun y => v.toH1.toFun y - v.boundaryData.toFun y) := by
    unfold cubeLpNorm normalizedCubeMeasure cubeMeasure
    exact congrArg ENNReal.toReal
      (eLpNorm_congr_ae (Measure.ae_smul_measure hwval _))
  have hgradeq : cubeBesovNegativeVectorSeminormTwo Q (s / 2)
        (fun x => w.toH1Function.grad x) =
      cubeBesovNegativeVectorSeminormTwo Q (s / 2)
        (fun x => v.toH1.grad x - v.boundaryData.grad x) :=
    cubeBesovNegativeVectorSeminormTwo_eq_of_ae_eq_on_cubeSet (s / 2)
      (by simpa [w, volumeMeasureOn] using
        v.zeroTraceDifferenceH10CubeSet_grad_ae_eq)
  have hsub := cubeBesovNegativeVectorSeminormTwo_sub_le_sqrtTwo_mul_add_of_bddAbove
    Q (s / 2) (fun x => v.toH1.grad x) (fun x => v.boundaryData.grad x)
    hvL2 hhL2 hvBdd hhBdd
  have hC0 : 0 ≤ negativeNormToL2Constant d :=
    (negativeNormToL2Constant_pos d).le
  calc
    cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - v.boundaryData.toFun y) =
        cubeBesovScaleWeight (1 : ℝ) Q *
          cubeLpNorm Q (2 : ℝ≥0∞) (fun y => w.toH1Function.toFun y) := by rw [hLHS]
    _ ≤ negativeNormToL2Constant d *
          cubeBesovNegativeVectorSeminormTwo Q (s / 2)
            (fun x => w.toH1Function.grad x) := hval
    _ = negativeNormToL2Constant d *
          cubeBesovNegativeVectorSeminormTwo Q (s / 2)
            (fun x => v.toH1.grad x - v.boundaryData.grad x) := by rw [hgradeq]
    _ ≤ negativeNormToL2Constant d *
          (Real.sqrt 2 *
            (cubeBesovNegativeVectorSeminormTwo Q (s / 2) (fun x => v.toH1.grad x) +
              cubeBesovNegativeVectorSeminormTwo Q (s / 2)
                (fun x => v.boundaryData.grad x))) :=
      mul_le_mul_of_nonneg_left hsub hC0
    _ = boundaryDifferencePriceConst d *
          (cubeBesovNegativeVectorSeminormTwo Q (s / 2) (fun x => v.toH1.grad x) +
            cubeBesovNegativeVectorSeminormTwo Q (s / 2)
              (fun x => v.boundaryData.grad x)) := by
      rw [boundaryDifferencePriceConst]
      ring

private def forcedOfDirichlet {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g) :
    ForcedCubeSolution Q a g where
  toH1 := v.toH1
  weakSolution := v.weakSolution

/-- Forced coarse-Poincare price of the solution-gradient negative seminorm. -/
theorem exists_negativeBesov_grad_le_coarsePoincare (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube d) (a : CoeffFamily d) (s : ℝ) (g : Vec d → Vec d)
        (v : DirichletForcedCubeSolution Q a g),
        0 < s → s ≤ 1 → ForceBesovRegularity Q (s / 2) g →
          cubeBesovNegativeVectorSeminormTwo Q (s / 2) (fun x => v.toH1.grad x) ≤
            C * Real.rpow (s / 2) (-(3 / 2 : ℝ)) *
                poincareLowerEllipticityFactor Q a (s / 4) (.finite 2) *
                dirichletForcedSolutionEnergyNorm Q a v +
              C * Real.rpow (s / 2) (-3 : ℝ) *
                Real.rpow (Ch02.lambdaSq Q (s / 4) (.finite 2) a) (-1 : ℝ) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 2) g := by
  obtain ⟨C, hC, hgrad, _⟩ := (coarsePoincareRHSTheory (d := d)).exists_constant
  refine ⟨C, hC, ?_⟩
  intro Q a s g v hs hs1 hforce
  have hbase := hgrad (Q := Q) (a := a) (s := s / 2) (g := g)
    (forcedOfDirichlet v) (by linarith only [hs]) (by linarith only [hs1]) hforce
  rw [scaleNormalizedNegativeBesovVectorNorm_finite_two_eq_cubeBesovNegativeVectorSeminormTwo,
    coarsePoincareWithRHSGradientRHS, show s / 2 / 2 = s / 4 by ring] at hbase
  exact hbase

/-- The elementary geometric factor bounding a negative seminorm by the
normalized Euclidean `L2` norm. -/
noncomputable def boundaryNegativeToL2Factor (s : ℝ) : ℝ :=
  Real.sqrt ((geometricDiscount (s / 2) 2)⁻¹)

theorem boundaryNegativeToL2Factor_nonneg (s : ℝ) :
    0 ≤ boundaryNegativeToL2Factor s := Real.sqrt_nonneg _

theorem cubeBesovNegativeVectorSeminormTwo_le_normalizedEuclideanL2
    {Q : TriadicCube d} {s : ℝ} (hs : 0 < s) {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    cubeBesovNegativeVectorSeminormTwo Q (s / 2) F ≤
      boundaryNegativeToL2Factor s * boundaryNormalizedEuclideanL2 Q F := by
  have hFcube : MemVectorL2 (cubeSet Q) F := memVectorL2_cubeSet_of_openCubeSet hF
  have hmem : MemLp F (2 : ENNReal) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hFcube
  have hbase := sq_cubeBesovNegativeVectorSeminormTwo_le_l2Average_of_memLp Q
    (s := s / 2) (by linarith only [hs]) F hmem
  rw [← boundaryNormalizedEuclideanL2_sq hFcube] at hbase
  have hdisc : 0 < geometricDiscount (s / 2) 2 :=
    geometricDiscount_pos (by linarith only [hs])
  have hK : 0 ≤ (geometricDiscount (s / 2) 2)⁻¹ := (inv_pos.mpr hdisc).le
  have hrhs : 0 ≤ boundaryNegativeToL2Factor s * boundaryNormalizedEuclideanL2 Q F :=
    mul_nonneg (boundaryNegativeToL2Factor_nonneg s)
      (boundaryNormalizedEuclideanL2_nonneg Q F)
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hrhs ?_
  rw [mul_pow, boundaryNegativeToL2Factor, Real.sq_sqrt hK]
  exact hbase

/-- Composed price of the structural difference between a forced Dirichlet
solution and its boundary datum. -/
theorem exists_cubeLpNorm_datumDifference_le_dirichletEnergyRHS
    (d : ℕ) [NeZero d] :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (Q : TriadicCube d) (a : CoeffFamily d) (s : ℝ) (g : Vec d → Vec d)
        (v : DirichletForcedCubeSolution Q a g),
        0 < s → s ≤ 1 → ForceBesovRegularity Q (s / 2) g →
        ForceBesovRegularity Q (s / 2) (dirichletBoundaryGradientField v) →
          cubeBesovScaleWeight (1 : ℝ) Q *
              cubeLpNorm Q (2 : ℝ≥0∞)
                (fun y => v.toH1.toFun y - v.boundaryData.toFun y) ≤
            C₁ *
              (Real.rpow (s / 2) (-(3 / 2 : ℝ)) *
                    poincareLowerEllipticityFactor Q a (s / 4) (.finite 2) *
                    dirichletEnergyWithRHSRHS C₂ Q a (s / 2) g v +
                  Real.rpow (s / 2) (-3 : ℝ) *
                    Real.rpow (Ch02.lambdaSq Q (s / 4) (.finite 2) a) (-1 : ℝ) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 2) g +
                  boundaryNegativeToL2Factor s *
                    boundaryNormalizedEuclideanL2 Q
                      (dirichletBoundaryGradientField v)) := by
  obtain ⟨Cp, hCp, hpoin⟩ := exists_negativeBesov_grad_le_coarsePoincare d
  obtain ⟨Ce, hCe, hdir, _⟩ := (energyConsequencesRHSTheory (d := d)).exists_constant
  refine ⟨boundaryDifferencePriceConst d * max 1 Cp, Ce,
    mul_pos (boundaryDifferencePriceConst_pos d)
      (lt_of_lt_of_le zero_lt_one (le_max_left 1 Cp)), hCe, ?_⟩
  intro Q a s g v hs hs1 hforce hforceH
  set K : ℝ := max 1 Cp with hK
  have hK1 : (1 : ℝ) ≤ K := le_max_left 1 Cp
  have hKp : Cp ≤ K := le_max_right 1 Cp
  have hK0 : (0 : ℝ) ≤ K := by linarith only [hK1]
  set lamHalf : ℝ :=
    poincareLowerEllipticityFactor Q a (s / 4) (.finite 2) with hlamHalf
  set lamInv : ℝ :=
    Real.rpow (Ch02.lambdaSq Q (s / 4) (.finite 2) a) (-1 : ℝ) with hlamInv
  set Bg : ℝ := scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 2) g with hBg
  set E : ℝ := dirichletForcedSolutionEnergyNorm Q a v with hE
  set D : ℝ := dirichletEnergyWithRHSRHS Ce Q a (s / 2) g v with hD
  set Hn : ℝ := boundaryNormalizedEuclideanL2 Q
    (dirichletBoundaryGradientField v) with hHn
  have hlamHalf0 : 0 ≤ lamHalf := by
    rw [hlamHalf, poincareLowerEllipticityFactor]
    exact Real.rpow_nonneg
      (Ch02.lambdaSq_nonneg Q a (by linarith only [hs]) (by norm_num)) _
  have hlamInv0 : 0 ≤ lamInv := by
    rw [hlamInv]
    exact Real.rpow_nonneg
      (Ch02.lambdaSq_nonneg Q a (by linarith only [hs]) (by norm_num)) _
  have hpow32 : 0 ≤ Real.rpow (s / 2) (-(3 / 2 : ℝ)) :=
    Real.rpow_nonneg (by linarith only [hs]) _
  have hpow3 : 0 ≤ Real.rpow (s / 2) (-3 : ℝ) :=
    Real.rpow_nonneg (by linarith only [hs]) _
  have hED : E ≤ D := hdir (Q := Q) (a := a) (s := s / 2) (g := g) v
    (by linarith only [hs]) (by linarith only [hs1]) hforce hforceH
  have hsol : cubeBesovNegativeVectorSeminormTwo Q (s / 2)
      (fun x => v.toH1.grad x) ≤
      K * (Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D +
        Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg) := by
    have hbase := hpoin Q a s g v hs hs1 hforce
    have hstep1 : Cp * Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * E ≤
        K * (Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D) := by
      have h1 : Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * E ≤
          Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D :=
        mul_le_mul_of_nonneg_left hED (mul_nonneg hpow32 hlamHalf0)
      have h2 : 0 ≤ Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D := by
        refine le_trans ?_ h1
        refine mul_nonneg (mul_nonneg hpow32 hlamHalf0) ?_
        rw [hE, dirichletForcedSolutionEnergyNorm, h1EnergyNormOnCube]
        exact Real.sqrt_nonneg _
      calc
        Cp * Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * E =
            Cp * (Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * E) := by ring
        _ ≤ K * (Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D) :=
          mul_le_mul hKp h1 (by
            refine mul_nonneg (mul_nonneg hpow32 hlamHalf0) ?_
            rw [hE, dirichletForcedSolutionEnergyNorm, h1EnergyNormOnCube]
            exact Real.sqrt_nonneg _) hK0
    have hstep2 : Cp * Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg ≤
        K * (Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg) := by
      have hBg0 : 0 ≤ Bg := by
        rw [hBg]
        exact scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
          hforce
      calc
        Cp * Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg =
            Cp * (Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg) := by ring
        _ ≤ K * (Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg) :=
          mul_le_mul_of_nonneg_right hKp
            (mul_nonneg (mul_nonneg hpow3 hlamInv0) hBg0)
    calc
      cubeBesovNegativeVectorSeminormTwo Q (s / 2) (fun x => v.toH1.grad x) ≤
          Cp * Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * E +
            Cp * Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg := hbase
      _ ≤ K * (Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D) +
            K * (Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg) :=
        add_le_add hstep1 hstep2
      _ = K * (Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D +
            Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg) := by ring
  have hdatum : cubeBesovNegativeVectorSeminormTwo Q (s / 2)
      (fun x => v.boundaryData.grad x) ≤
      K * (boundaryNegativeToL2Factor s * Hn) := by
    have hbase := cubeBesovNegativeVectorSeminormTwo_le_normalizedEuclideanL2
      (Q := Q) (s := s) hs (F := fun x => v.boundaryData.grad x)
      v.boundaryData.grad_memVectorL2
    have h0 : 0 ≤ boundaryNegativeToL2Factor s * Hn := by
      rw [hHn, dirichletBoundaryGradientField]
      exact mul_nonneg (boundaryNegativeToL2Factor_nonneg s)
        (boundaryNormalizedEuclideanL2_nonneg Q _)
    refine hbase.trans ?_
    rw [hHn, dirichletBoundaryGradientField]
    simpa only [hHn, dirichletBoundaryGradientField, one_mul] using!
      mul_le_mul_of_nonneg_right hK1 h0
  have hmain := cubeBesovScaleWeight_mul_cubeLpNorm_datumDifference_le_negativeBesov
    Q (a := a) (g := g) v hs hs1
  refine hmain.trans ?_
  calc
    boundaryDifferencePriceConst d *
        (cubeBesovNegativeVectorSeminormTwo Q (s / 2) (fun x => v.toH1.grad x) +
          cubeBesovNegativeVectorSeminormTwo Q (s / 2)
            (fun x => v.boundaryData.grad x)) ≤
      boundaryDifferencePriceConst d *
        (K * (Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D +
            Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg) +
          K * (boundaryNegativeToL2Factor s * Hn)) :=
      mul_le_mul_of_nonneg_left (add_le_add hsol hdatum)
        (boundaryDifferencePriceConst_pos d).le
    _ = boundaryDifferencePriceConst d * K *
        (Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D +
          Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg +
          boundaryNegativeToL2Factor s * Hn) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
