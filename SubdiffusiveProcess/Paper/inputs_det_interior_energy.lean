import SubdiffusiveProcess.Paper.inputs_det_interior_cover
import SubdiffusiveProcess.Paper.inputs_det_energy_translation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryProjectedComponentAssembly
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCaccioppoli
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.BoundaryCellRow

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper

theorem inputs_det_interior_energy (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∀ Cerr : ℝ, 0 < Cerr → ∃ K : ℝ, 0 < K ∧
      ∀ (s : ℝ) (hs : 0 < s) (hsle : s ≤ (1 / 4 : ℝ))
        (m n : ℕ), n + 5 ≤ m → ∀ z ∈ cube d m,
      ∀ x ∈ truncatedCube d m (n - 3) z,
      ∀ (a : Vec d → ℝ) (data : ScalarTriadicCoeffData (fun q => a (q + z)))
        (a0 : ℝ), 0 < a0 →
      paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal Cerr →
      ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) →
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn a (cube d m) u g →
      (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
        Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
          (originCube d m) sOrder FiniteLpExponent.two g) →
      ∀ y ∈ cube d m,
        translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
      ∀ (dataY : ScalarTriadicCoeffData (fun q => a (q + y)))
        (u0 : H1Function (openCubeSet (originCube d ((n : ℤ) - 2)))),
        (∀ p, u0.grad p = u.grad (p + y)) →
      ∀ (s1 smid : FractionalOrder), s1.1 < smid.1 →
      let U := truncatedCube d m n x;
      Homogenization.Book.Ch03.ABK26.weightedLocalSymmetricEnergyLp
        (originCube d ((n : ℤ) - 2)) ((originCube d ((n : ℤ) - 2)).scale - 1) (by omega)
        (dataY.toTriadicCoeffFamily.coeffOn (originCube d ((n : ℤ) - 2)))
        u0 s1 smid FiniteLpExponent.two ≤
      ENNReal.ofReal (SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.dirichletWeightedEnergyFactor s1.1 smid.1 *
        Real.sqrt (K *
          (a0 * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
            normalizedL2On U (fun q => u.toFun q - averageOn U u.toFun) ^ 2 +
           s ^ (-12 : ℝ) * a0⁻¹ * (3 : ℝ) ^ (2 * s * (n : ℝ)) *
            (fractionalSeminormOn U s g).toReal ^ 2)))) := by
  intro Cerr hCerr
  obtain ⟨K, hK, hcover⟩ := inputs_det_interior_cover d hd Cerr hCerr
  refine ⟨K, hK, ?_⟩
  intro s hs hsle m n hnm z hz x hx a data a0 ha0 herr hnot u g hw hg
    y hy hD dataY u0 hu0 s1 smid hgap
  have he := hcover s hs hsle m n hnm z hz x hx a data a0 ha0 herr hnot u g hw hg y hy hD
  have ht := inputs_det_energy_translation d a y dataY ((n : ℤ) - 2) u0 u.grad hu0
  have hr := SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.weightedLocalSymmetricEnergyLp_two_le_rootEnergyReadout
    (originCube d ((n : ℤ) - 2))
    (dataY.toTriadicCoeffFamily.coeffOn (originCube d ((n : ℤ) - 2))) u0 s1 smid (sub_pos.mpr hgap)
  refine hr.trans (ENNReal.ofReal_le_ofReal ?_)
  apply mul_le_mul_of_nonneg_left _
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.dirichletWeightedEnergyFactor_nonneg _ _)
  rw [ht]
  exact Real.sqrt_le_sqrt he

end Paper
