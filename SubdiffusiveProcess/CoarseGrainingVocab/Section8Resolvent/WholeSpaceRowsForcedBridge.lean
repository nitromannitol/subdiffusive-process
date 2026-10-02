import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.ScalarDivergenceLift
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WeightedMassiveSolution




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

noncomputable section

variable {d : ℕ}

/-- The value `L²` norm of a cube `H¹` function, as a real number. -/
theorem norm_toScalarL2_const_mul {U : Set (Vec d)} {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict U)) (mu : ℝ) :
    ‖toScalarL2 (hu.const_mul mu)‖ = |mu| * ‖toScalarL2 hu‖ := by
  classical
  rw [toScalarL2, toScalarL2, Lp.norm_toLp, Lp.norm_toLp]
  have hsmul : (fun x ↦ mu * u x) = mu • u := by
    funext x
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hsmul, eLpNorm_const_smul, ENNReal.toReal_mul]
  simp [Real.norm_eq_abs]



theorem exists_isForcedEquation_of_isMassiveWeakSolutionOn (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : TriadicCube d) (A : Ch02.CoeffOn (Ch02.cubeDomain Q))
        (a : Vec d → ℝ),
        (∀ x, A.toCoeffField x = scalarCoeffField a x) →
        ∀ (mu : ℝ) (u : H1Function (openCubeSet Q)),
          IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu (openCubeSet Q) u
            (fun _ ↦ (0 : ℝ)) →
          ∃ F : CubeVectorH1Function Q,
            Ch03.ABK26.IsForcedEquation Q A u F.toField ∧
              F.gradientCoordL2NormSum ≤ C * (|mu| * ‖toScalarL2 u.memL2‖) := by
  classical
  obtain ⟨C, hC0, hlift⟩ := exists_cubeVectorH1Function_divergence_lift d
  refine ⟨C, hC0, ?_⟩
  intro Q A a hA mu u hu
  have hmem : MemLp (fun x ↦ mu * u.toFun x) 2 (volume.restrict (openCubeSet Q)) :=
    u.memL2.const_mul mu
  obtain ⟨F0, hpair, hnorm⟩ := hlift Q (fun x ↦ mu * u.toFun x) hmem
  refine ⟨negCubeVectorH1Function F0, ?_, ?_⟩
  · intro phi
    have heq := hu phi
    simp only [one_mul, zero_mul, integral_zero] at heq
    have hmass :
        (∫ x in openCubeSet Q, (fun y ↦ mu * u.toFun y) x *
            phi.toH1Function.toFun x ∂volume) =
          mu * ∫ x in openCubeSet Q, u.toFun x * phi.toH1Function.toFun x
            ∂volume := by
      simp_rw [mul_assoc]
      exact integral_const_mul _ _
    have hlhs :
        (∫ x in openCubeSet Q,
            vecDot (matVecMul (A.toCoeffField x) (u.grad x))
              (phi.toH1Function.grad x) ∂volume) =
          ∫ x in openCubeSet Q,
            vecDot (a x • u.grad x) (phi.toH1Function.grad x) ∂volume := by
      refine setIntegral_congr_fun
        (Homogenization.isOpenBoundedConvexDomain_openCubeSet Q).isOpen.measurableSet
        fun x _ ↦ ?_
      rw [hA x, scalarCoeffField, matVecMul_scalarMatrix]
    have hneg :
        (∫ x in openCubeSet Q,
            vecDot ((negCubeVectorH1Function F0).toField x)
              (phi.toH1Function.grad x) ∂volume) =
          -∫ x in openCubeSet Q,
            vecDot (F0.toField x) (phi.toH1Function.grad x) ∂volume := by
      rw [negCubeVectorH1Function_toField]
      simp_rw [vecDot_neg_left]
      exact integral_neg _
    rw [hlhs, hneg, neg_neg]
    have hp := hpair phi
    rw [hmass] at hp
    linarith [heq, hp]
  · rw [negCubeVectorH1Function_gradientCoordL2NormSum]
    refine hnorm.trans (le_of_eq ?_)
    rw [norm_toScalarL2_const_mul u.memL2 mu]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
