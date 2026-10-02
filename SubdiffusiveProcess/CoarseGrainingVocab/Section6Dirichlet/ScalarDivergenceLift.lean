import SubdiffusiveProcess.CoarseGrainingVocab.DirichletScalarForcing
import Homogenization.Book.Ch01.Theorems.CubeDirichletH2

/-!
# An `H¹` divergence lift of scalar `L²` data

The Dirichlet coarse-graining theorem is formulated for a vector divergence
datum, whereas the cutoff theorem starts from a scalar `L²` forcing.  We solve
the zero-boundary Poisson problem, use the proved cube `H²` estimate, and take
the negative gradient.  The resulting coordinatewise `H¹` vector field has
the manuscript sign `div F = f` in the weak sense.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- Coordinatewise negation of a cube `H¹` vector field. -/
def negCubeVectorH1Function {d : ℕ} {Q : TriadicCube d}
    (F : CubeVectorH1Function Q) : CubeVectorH1Function Q where
  coord := fun i ↦ -(F.coord i)

@[simp] theorem negCubeVectorH1Function_toField
    {d : ℕ} {Q : TriadicCube d} (F : CubeVectorH1Function Q) :
    (negCubeVectorH1Function F).toField = fun x ↦ -F.toField x := by
  funext x i
  simp [negCubeVectorH1Function, CubeVectorH1Function.toField]

@[simp] theorem negCubeVectorH1Function_gradientCoordL2NormSum
    {d : ℕ} {Q : TriadicCube d} (F : CubeVectorH1Function Q) :
    (negCubeVectorH1Function F).gradientCoordL2NormSum =
      F.gradientCoordL2NormSum := by
  unfold negCubeVectorH1Function CubeVectorH1Function.gradientCoordL2NormSum
  apply Finset.sum_congr rfl
  intro i _
  unfold H1Function.gradientCoordL2NormSum
  apply Finset.sum_congr rfl
  intro j _
  change ‖(-(F.coord i)).gradCoordToScalarL2 j‖ =
    ‖(F.coord i).gradCoordToScalarL2 j‖
  rw [show -(F.coord i) = (-1 : ℝ) • F.coord i by rfl,
    H1Function.gradCoordToScalarL2_smul]
  simp

/-- Dimension-only `H¹` divergence lift.  The pairing is the weak statement
`div F = f`, with exactly the sign consumed by Chapter 3's
`IsForcedEquation`. -/
theorem exists_cubeVectorH1Function_divergence_lift
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : TriadicCube d) (f : Vec d → ℝ)
        (hf : MemLp f 2 (volume.restrict (openCubeSet Q))),
        ∃ F : CubeVectorH1Function Q,
          (∀ phi : H10Function (openCubeSet Q),
            ∫ x in openCubeSet Q, f x * phi.toH1Function.toFun x ∂volume =
              -∫ x in openCubeSet Q,
                vecDot (F.toField x) (phi.toH1Function.grad x) ∂volume) ∧
          F.gradientCoordL2NormSum ≤
            C * ‖toScalarL2 hf‖ := by
  obtain ⟨C, hC⟩ :=
    Homogenization.CubeDirichletWeakPoissonProblem.exists_cubeDirichletH2RegularityVolumeL2InDimension d
  refine ⟨C, hC.1, ?_⟩
  intro Q f hf
  obtain ⟨u, hu⟩ :=
    exists_isScalarDirichletSolutionOn_one
      (Q := Q) (hD := (0 : H1Function (openCubeSet Q))) hf
  obtain ⟨w, hvalue, hgrad⟩ := hu.1
  have hweak : CubeDirichletWeakPoissonProblem Q w f := by
    intro phi
    have heq := hu.2 phi
    simp_rw [hgrad] at heq
    simp only [Pi.zero_apply, H1Function.zero_grad, zero_add] at heq
    simp_rw [show ∀ x : Vec d, matVecMul (1 : Mat d) (w.toH1Function.grad x) =
        w.toH1Function.grad x from fun x ↦ Matrix.one_mulVec _] at heq
    exact heq
  have hfNormalized : MemLp f 2 (normalizedCubeMeasure Q) := by
    rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  obtain ⟨H, hH⟩ := (hC.2 Q).2 w f hfNormalized hweak
  let G : CubeVectorH1Function Q := CubeVectorH1Function.ofWeakHessianGradient H
  let F : CubeVectorH1Function Q := negCubeVectorH1Function G
  refine ⟨F, ?_, ?_⟩
  · intro phi
    have heq := hweak phi
    rw [← heq]
    simp only [F, G, negCubeVectorH1Function_toField,
      CubeVectorH1Function.ofWeakHessianGradient_toField]
    have hintegral :
        (∫ x in openCubeSet Q,
          vecDot (-w.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume) =
          -(∫ x in openCubeSet Q,
            vecDot (w.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume) := by
      simp_rw [vecDot_neg_left]
      exact integral_neg _
    rw [hintegral, neg_neg]
  · change (negCubeVectorH1Function G).gradientCoordL2NormSum ≤
      C * ‖toScalarL2 hf‖
    rw [negCubeVectorH1Function_gradientCoordL2NormSum]
    simpa only [G,
      CubeVectorH1Function.gradientCoordL2NormSum_ofWeakHessianGradient] using hH

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
