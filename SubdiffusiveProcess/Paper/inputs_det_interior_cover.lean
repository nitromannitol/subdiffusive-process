module

public import SubdiffusiveProcess.Paper.inputs_det_scalar_translation
public import SubdiffusiveProcess.Paper.inputs_det_energy_integrable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCellCover
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCellGeometry
public import SubdiffusiveProcess.Paper.inputs_det_interior_cell
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCaccioppoli
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.BoundaryCellRow

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book Homogenization.Book.Ch03
open scoped BigOperators ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.Paper

theorem inputs_det_interior_cover (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∀ Cerr : ℝ, 0 < Cerr → ∃ K : ℝ, 0 < K ∧
      ∀ (s : ℝ) (_hs : 0 < s) (_hsle : s ≤ (1 / 4 : ℝ))
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
      let U := truncatedCube d m n x;
      normalizedSetAverage (translatedCube d ((n : ℤ) - 2) y)
        (fun q => a q * vecNormSq (u.grad q)) ≤
      K *
          (a0 * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
            normalizedL2On U (fun q => u.toFun q - averageOn U u.toFun) ^ 2 +
           s ^ (-12 : ℝ) * a0⁻¹ * (3 : ℝ) ^ (2 * s * (n : ℝ)) *
            (fractionalSeminormOn U s g).toReal ^ 2)) := by
  intro Cerr hCerr
  obtain ⟨K, hK, hcell⟩ := inputs_det_interior_cell d hd Cerr hCerr
  refine ⟨K, hK, ?_⟩
  intro s hs hsle m n hnm z hz x hx a data a0 ha0 herr hnot u g hw hg y hy hD
  let k : ℤ := (n : ℤ) - 2
  let Q := originCube d k
  let U := truncatedCube d m n x
  let B := K * (a0 * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
    normalizedL2On U (fun q => u.toFun q - averageOn U u.toFun) ^ 2 +
    s ^ (-12 : ℝ) * a0⁻¹ * (3 : ℝ) ^ (2 * s * (n : ℝ)) *
      (fractionalSeminormOn U s g).toReal ^ 2)
  let F := fun q => a q * vecNormSq (u.grad q)
  have hset : translateSet y (openCubeSet Q) = translatedCube d k y := by
    rw [translatedCube, cube, SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.image_add_eq_translateSet]
  have hnext : translateSet y (openCubeSet Q) ⊆ truncatedCube d m ((n : ℤ) - 1) x := by
    rw [hset]
    exact hD
  have hsub : translateSet y (openCubeSet Q) ⊆ openCubeSet (originCube d m) := by
    intro q hq
    exact (hnext hq).2
  let up := u.restrict ((isOpenBoundedConvexDomain_openCubeSet Q).translateSet y).isOpen hsub
  let u0 := H1Function.untranslate y up
  have hgrad : ∀ q, u0.grad q = u.grad (q + y) := by
    intro q
    rw [H1Function.untranslate_grad]
    rfl
  obtain ⟨dataY0⟩ := inputs_det_scalar_translation d (fun q => a (q + z)) data (y - z)
  have dataY : ScalarTriadicCoeffData (fun q => a (q + y)) := by
    simpa only [add_assoc, sub_add_cancel] using dataY0
  have hint := inputs_det_energy_integrable d a y dataY k u0 u.grad hgrad
  change normalizedSetAverage (translatedCube d k y) F ≤ B
  change Homogenization.volumeAverage (translatedCube d k y) F ≤ B
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.volumeAverage_translatedCube_eq_depthTwoDescendantsAverage k y F hint]
  calc
    _ ≤ descendantsAverage Q 2 (fun _ => B) := by
      apply descendantsAverage_le_descendantsAverage
      intro R hR
      let qR := y + triadicCubeShift R
      have hqR : qR ∈ truncatedCube d m ((n : ℤ) - 1) x :=
        SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.translated_descendantCentre_mem_of_parent_subset hR hnext
      have hxDomain : x ∈ cube d m := hx.2
      have hpatch : openCubeAtScale qR ((n : ℤ) - 3) ⊆ cube d m :=
        SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.openCubeAtScale_predTwo_subset_domain_of_not_boundaryTouches
          hxDomain hqR hnot
      have hb := hcell s hs hsle m n hnm z hz x hx a data a0 ha0 herr hnot u g hw hg qR hqR hpatch
      have hRset : translateSet y (openCubeSet R) = truncatedCube d m (k - 2) qR :=
        SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.translate_descendant_openCubeSet_eq_truncatedCube hR hsub
      rw [hRset]
      simpa only [k, Q, U, B, F, show (n : ℤ) - 2 - 2 = (n : ℤ) - 4 by omega] using hb
    _ = _ := descendantsAverage_const Q 2 B

end SubdiffusiveProcess.Paper
