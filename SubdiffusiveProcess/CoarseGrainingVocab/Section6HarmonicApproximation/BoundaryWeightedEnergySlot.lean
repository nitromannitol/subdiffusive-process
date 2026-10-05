module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.PhysicalRadiusRecurrence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.WeightedEnergySlot

@[expose] public section

/-!
# Boundary physical energy to the sharp-loop weighted slot

This module performs the exact normalization change after the physical radius
row has been collapsed.  It introduces no additional PDE premise.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem symmPart_scalarMatrix_weightedSlot {d : ℕ} (a : ℝ) :
    symmPart (scalarMatrix (d := d) a) = scalarMatrix (d := d) a := by
  ext i j
  by_cases h : i = j
  · simp [symmPart, scalarMatrix, h]
  · simp [symmPart, scalarMatrix, h, Ne.symm h]

private theorem vecDot_matVecMul_scalarMatrix_weightedSlot {d : ℕ}
    (a : ℝ) (v : Vec d) :
    vecDot v (matVecMul (scalarMatrix (d := d) a) v) = a * vecNormSq v := by
  simp only [scalarMatrix, vecDot, matVecMul, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, mul_comm,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum, vecNormSq]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A physical inverse-square-root energy readout supplies the real weighted
energy slot of the sharp comparator. -/
theorem weightedLocalSymmetricEnergyLp_two_le_of_physicalEnergyReadout
    {d : ℕ} [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (L : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (k : ℤ) (y : Vec d)
    (u0 : H1Function (openCubeSet (originCube d k)))
    (gradU : Vec d → Vec d)
    (hu0grad : ∀ p, u0.grad p = gradU (p + y))
    (s1 smid : FractionalOrder) (hgap : s1.1 < smid.1)
    {sigma R : ℝ} (hsigma : 0 < sigma)
    (henergy : sigma ^ (-1 / 2 : ℝ) *
      vectorNormalizedL2On (translatedCube d k y) (fun p ↦
        Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) • gradU p) ≤ R) :
    Ch03.ABK26.weightedLocalSymmetricEnergyLp (originCube d k)
        ((originCube d k).scale - 1) (by omega)
        ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
          (originCube d k))
        u0 s1 smid FiniteLpExponent.two ≤
      ENNReal.ofReal
        (Section6Dirichlet.dirichletWeightedEnergyFactor s1.1 smid.1 *
          (Real.sqrt sigma * R)) := by
  have hroot := weightedLocalSymmetricEnergyLp_two_le_rootEnergyReadout
    (originCube d k)
    ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
      (originCube d k))
    u0 s1 smid (by linarith)
  refine hroot.trans (ENNReal.ofReal_le_ofReal ?_)
  apply mul_le_mul_of_nonneg_left _
    (Section6Dirichlet.dirichletWeightedEnergyFactor_nonneg _ _)
  have hframe := cubeAverage_coefficientEnergyDensity_aCutoffFamily_eq_translatedCube
    M L omega k y u0 gradU hu0grad
  rw [hframe]
  rw [← Section6Holder.vectorNormalizedL2On_sqrt_smul_eq_sqrt_volumeAverage
    (translatedCube d k y)
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) gradU
      (fun p ↦ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega p).le)]
  have hcancel : Real.sqrt sigma * sigma ^ (-1 / 2 : ℝ) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hsigma]
    norm_num
  calc
    vectorNormalizedL2On (translatedCube d k y) (fun p ↦
          Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) • gradU p) =
        Real.sqrt sigma * (sigma ^ (-1 / 2 : ℝ) *
          vectorNormalizedL2On (translatedCube d k y) (fun p ↦
            Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) • gradU p)) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ Real.sqrt sigma * R :=
      mul_le_mul_of_nonneg_left henergy (Real.sqrt_nonneg _)

/-- The concrete four-budget weighted slot, conditional only on an admissible
physical radius recurrence.  The recurrence exponent is deliberately free:
the face-slab construction naturally retains one additional inverse-gap
power, while radius iteration changes only the resulting absolute constant. -/
theorem exists_boundaryWeightedEnergySlot_of_physicalRecurrence
    {d : ℕ} [NeZero d] {theta tau CA CB beta : ℝ}
    (hbeta : 0 ≤ beta) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (htau0 : 0 < tau) (htau1 : tau < 1)
    (htheta0 : 0 ≤ theta) (hcontract : theta < Real.rpow tau beta)
    (hrec : HarmonicPhysicalRadiusRecurrence d theta CA CB beta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x y : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        translatedCube d ((n : ℤ) - 2) y ⊆
          truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        MemFractionalOn (cube d (m : ℤ)) sOrder.1 h.grad →
      ∀ (u0 : H1Function (openCubeSet (originCube d ((n : ℤ) - 2)))),
        (∀ p, u0.grad p = u.grad (p + y)) →
      ∀ (s1 smid : FractionalOrder), s1.1 < smid.1 →
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        let B := (3 : ℝ) ^ (-(n : ℤ)) *
              normalizedL2On U
                (fun q ↦ u.toFun q - averageOn U u.toFun) +
            (if BoundaryTouches U (cube d (m : ℤ)) then
              Real.sqrt (vecNormSq (averageVecOn U h.grad)) else 0) +
            sigma⁻¹ * (Real.rpow sOrder.1 (-6 : ℝ) *
              Real.rpow (3 : ℝ) (sOrder.1 * (n : ℝ)) *
              (fractionalSeminormOn U sOrder.1 g).toReal) +
            (if BoundaryTouches U (cube d (m : ℤ)) then
              Real.rpow sOrder.1 (-2 : ℝ) *
                Real.rpow (3 : ℝ) (sOrder.1 * (n : ℝ)) *
                (fractionalSeminormOn U sOrder.1 h.grad).toReal else 0)
        Ch03.ABK26.weightedLocalSymmetricEnergyLp
            (originCube d ((n : ℤ) - 2))
            ((originCube d ((n : ℤ) - 2)).scale - 1) (by omega)
            ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
              (originCube d ((n : ℤ) - 2))) u0 s1 smid
              FiniteLpExponent.two ≤
          ENNReal.ofReal
            (Section6Dirichlet.dirichletWeightedEnergyFactor s1.1 smid.1 *
              (Real.sqrt sigma * (C * B))) := by
  obtain ⟨C, hC, henergy⟩ :=
    exists_translatedCubeEnergyReadout_of_physicalRecurrence d
      (theta := theta) (tau := tau) (CA := CA) (CB := CB) (beta := beta)
      hbeta hCA hCB htau0 htau1 htheta0 hcontract hrec
  refine ⟨C, hC, ?_⟩
  intro M sOrder hs L m n hmL hnm z x y omega hz hx hD hgood u h g hdir hg
    hh u0 hu0grad s1 smid hgap
  dsimp only
  have hout := henergy M sOrder hs L m n hmL hnm z x y omega hz hx hD hgood
    u h g hdir hg hh
  dsimp only at hout
  exact weightedLocalSymmetricEnergyLp_two_le_of_physicalEnergyReadout
    M L omega ((n : ℤ) - 2) y u0 u.grad hu0grad s1 smid hgap
      (sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z))
      (R := C * ((3 : ℝ) ^ (-(n : ℤ)) *
              normalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
                (fun q ↦ u.toFun q - averageOn
                  (truncatedCube d (m : ℤ) (n : ℤ) x) u.toFun) +
            (if BoundaryTouches (truncatedCube d (m : ℤ) (n : ℤ) x)
                (cube d (m : ℤ)) then
              Real.sqrt (vecNormSq (averageVecOn
                (truncatedCube d (m : ℤ) (n : ℤ) x) h.grad)) else 0) +
            (tailAverage M L (n + 2) omega
              (translatedCube d ((n : ℤ) + 2) z))⁻¹ *
              (Real.rpow sOrder.1 (-6 : ℝ) * Real.rpow (3 : ℝ)
                (sOrder.1 * (n : ℝ)) *
                (fractionalSeminormOn
                  (truncatedCube d (m : ℤ) (n : ℤ) x) sOrder.1 g).toReal) +
            (if BoundaryTouches (truncatedCube d (m : ℤ) (n : ℤ) x)
                (cube d (m : ℤ)) then
              Real.rpow sOrder.1 (-2 : ℝ) * Real.rpow (3 : ℝ)
                (sOrder.1 * (n : ℝ)) *
                (fractionalSeminormOn
                  (truncatedCube d (m : ℤ) (n : ℤ) x)
                    sOrder.1 h.grad).toReal else 0)))
      (by
        rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
        rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
        exact tailCoefficientCubeAverage_pos M L (n + 2)
          (translatePotentialSample z omega)) hout

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
