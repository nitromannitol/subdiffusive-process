import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAnalyticLocality
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeUnitTorsion
/-! Coefficient-local torsion comparison tests retain all zero-trace solution quantifiers. -/

set_option autoImplicit false
open Homogenization MeasureTheory Set Filter SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- An actual weighted-forcing versus constant-forcing torsion comparison.
All solution quantifiers are retained in this coefficient-local test. -/
def GoodCubeTorsionComparisonTest {d : ℕ} (Q : TriadicCube d)
    (a : Vec d → ℝ) (sigma eps : ℝ) : Prop :=
  ∀ u w : H10Function (openCubeSet Q),
    IsMassiveWeakSolutionOn a a 0 (openCubeSet Q) u.toH1Function (fun _ => 1) →
    IsMassiveWeakSolutionOn (fun _ => sigma) (fun _ => 1) 0
      (openCubeSet Q) w.toH1Function (fun _ => 1) →
    cubeLpNorm Q 2 (fun x => u.toH1Function.toFun x - w.toH1Function.toFun x) ≤
      eps * (cubeScaleFactor Q)^2 / sigma

/-- The complete comparison test depends only on the coefficient on the cube. -/
theorem goodCube_torsionComparisonTest_congr_coeff
    {d : ℕ} (Q : TriadicCube d) {a b : Vec d → ℝ}
    (hab : a =ᵐ[volume.restrict (openCubeSet Q)] b) (sigma eps : ℝ) :
    GoodCubeTorsionComparisonTest Q a sigma eps ↔
      GoodCubeTorsionComparisonTest Q b sigma eps := by
  constructor
  · intro h u w hu hw
    exact h u w ((goodCube_massiveWeakSolution_congr_coeff hab hab 0 _ _).mpr hu) hw
  · intro h u w hu hw
    exact h u w ((goodCube_massiveWeakSolution_congr_coeff hab hab 0 _ _).mp hu) hw

/-- Translated comparison tests are constant on observation fibres containing the physical cube. -/
theorem goodCube_torsionComparisonTest_translated_congr_coeff
    {d : ℕ} (Q : TriadicCube d) (z : Vec d) {a b : Vec d → ℝ} {S : Set (Vec d)}
    (hab : Set.EqOn a b S) (hsub : ∀ x ∈ openCubeSet Q, x + z ∈ S)
    (sigma eps : ℝ) :
    GoodCubeTorsionComparisonTest Q (fun x => a (x + z)) sigma eps ↔
      GoodCubeTorsionComparisonTest Q (fun x => b (x + z)) sigma eps := by
  apply goodCube_torsionComparisonTest_congr_coeff
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  exact hab (hsub x hx)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
