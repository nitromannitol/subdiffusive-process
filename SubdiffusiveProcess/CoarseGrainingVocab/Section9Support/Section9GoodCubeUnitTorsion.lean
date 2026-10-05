module

public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletScalarForcing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTorsionPaperComparison
public import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.OneCube
@[expose] public section

/-! Construct the actual unit-forcing intermediary and combine its comparison with the raw weighted-forcing Besov estimate. -/

set_option autoImplicit false
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- An elliptic scalar coefficient admits an actual zero-trace unit-forcing solution. -/
theorem goodCube_exists_unitTorsion
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {b : Vec d → ℝ} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) (scalarCoeffField b)) :
    ∃ u : H10Function (openCubeSet Q),
      IsMassiveWeakSolutionOn b (fun _ => 1) 0
        (openCubeSet Q) u.toH1Function (fun _ => 1) := by
  let : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  obtain ⟨v, hv⟩ := exists_isScalarDirichletSolutionOn hEll
    (0 : H1Function (openCubeSet Q)) (memLp_const (1 : ℝ) :
      MemLp (fun _ : Vec d => (1 : ℝ)) 2 (volume.restrict (openCubeSet Q)))
  obtain ⟨u, hval, hgrad⟩ := hv.1
  have hgrad' : v.grad = u.toH1Function.grad := by
    funext x
    simpa only [H1Function.zero_grad, Pi.zero_apply, zero_add] using hgrad x
  refine ⟨u, ?_⟩
  intro phi
  have heq := hv.2 phi
  rw [hgrad'] at heq
  simpa only [scalarCoeffField, matVecMul_scalarMatrix, zero_mul, zero_add, one_mul] using heq

/-- Triangle inequality for the normalized L2 distances between zero-trace carriers. -/
theorem goodCube_h10_cubeLpNorm_sub_triangle
    {d : ℕ} (Q : TriadicCube d) (u w v : H10Function (openCubeSet Q)) :
    cubeLpNorm Q 2 (u - v).toH1Function.toFun ≤
      cubeLpNorm Q 2 (u - w).toH1Function.toFun +
        cubeLpNorm Q 2 (w - v).toH1Function.toFun := by
  have hsum : (u - v).toH1Function.toFun =
      fun x => (u - w).toH1Function.toFun x + (w - v).toH1Function.toFun x := by
    funext x
    change u.toH1Function.toFun x + (-1) * v.toH1Function.toFun x =
      (u.toH1Function.toFun x + (-1) * w.toH1Function.toFun x) +
        (w.toH1Function.toFun x + (-1) * v.toH1Function.toFun x)
    ring
  rw [hsum]
  exact cubeLpNorm_add_le Q 2 _ _
    (h1_memLp_normalizedCubeMeasure Q (u - w).toH1Function)
    (h1_memLp_normalizedCubeMeasure Q (w - v).toH1Function) (by norm_num)

/-- Construct the unit-forcing intermediary and add its comparison to the weighted-forcing error. -/
theorem goodCube_torsion_l2_comparison_of_paper_test_and_unit_comparison
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) (Q : TriadicCube d)
    (A : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (A.coeffOn Q).toCoeffField x = scalarMatrix (b x))
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) (scalarCoeffField b))
    (hbL2 : MemL2On (openCubeSet Q) b)
    (h1 : MemL2On (openCubeSet Q) (fun _ : Vec d => (1 : ℝ)))
    (hg : MemLp (fun x => b x - 1) 2 (normalizedCubeMeasure Q))
    (hf : ExactCircIntegrable Q (fun x => b x - 1))
    {zeta H : ℝ} (hzeta : 0 ≤ zeta)
    (hBesov : ENNReal.ofReal ((3 : ℝ)^(-((Q.scale : ℝ) / 8))) *
      paperNegativeBesovCircDiagonal Q (1 / 8) (4 * (d : ℝ)) (fun x => b x - 1) hf ≤
        ENNReal.ofReal zeta)
    (e v : H10Function (openCubeSet Q))
    (he : IsMassiveWeakSolutionOn b b 0 (openCubeSet Q) e.toH1Function (fun _ => 1))
    (hcompare : ∀ w : H10Function (openCubeSet Q),
      IsMassiveWeakSolutionOn b (fun _ => 1) 0 (openCubeSet Q) w.toH1Function (fun _ => 1) →
        cubeLpNorm Q 2 (w - v).toH1Function.toFun ≤ H) :
    cubeLpNorm Q 2 (e - v).toH1Function.toFun ≤
      32 * (3 : ℝ)^((d : ℝ) + 1 / 2) * (weightedLocalSobolevEnergyConstant d)^2 *
        (1 - (3 : ℝ)^(-(3 / 8 : ℝ)))⁻¹ * zeta * (cubeScaleFactor Q)^2 *
          (Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹ + H := by
  obtain ⟨w, hw⟩ := goodCube_exists_unitTorsion Q hEll
  exact (goodCube_h10_cubeLpNorm_sub_triangle Q e w v).trans
    (add_le_add (goodCube_torsion_forcing_l2_comparison_of_paper_test
      hd Q A b hb hEll hbL2 h1 hg hf hzeta hBesov e w he hw) (hcompare w hw))

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
