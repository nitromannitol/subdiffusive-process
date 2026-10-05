module

public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.inputs_det_interior_energy
public import SubdiffusiveProcess.Paper.inputs_det_scalar_translation
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCaccioppoli
public import SubdiffusiveProcess.Analysis.InteriorComparisonMain

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.Paper

/-- The `y`-anchored certificate package obtained from the `z`-anchored one. -/
theorem aux_inputs_det_interior_comparison_dataY (d : ℕ) (a : Vec d → ℝ) (z y : Vec d)
    (data : ScalarTriadicCoeffData (fun q => a (q + z))) :
    Nonempty (ScalarTriadicCoeffData (fun q => a (q + y))) := by
  have h := inputs_det_scalar_translation d (fun q => a (q + z)) data (y - z)
  have hfun : (fun x => (fun q => a (q + z)) (x + (y - z))) = (fun q => a (q + y)) := by
    funext x
    show a (x + (y - z) + z) = a (x + y)
    congr 1
    abel
  rw [hfun] at h
  exact h

theorem inputs_det_interior_comparison (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∀ Cerr : ℝ, 0 < Cerr → ∃ C : ℝ, 0 < C ∧
    ∀ s : ℝ, 0 < s → s ≤ (1 / 4 : ℝ) →
    ∀ m n : ℕ, n + 5 ≤ m → ∀ z ∈ cube d m,
    ∀ x ∈ truncatedCube d m (n - 3) z,
    ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) →
    ∀ a : Vec d → ℝ, ∀ data : ScalarTriadicCoeffData (fun y => a (y + z)),
    ∀ a0 : ℝ, 0 < a0 →
    let err : ENNReal :=
      paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily a0;
    err ≤ ENNReal.ofReal Cerr →
    ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
      IsDivFormWeakSolutionOn a (cube d m) u g →
      (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
        Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
          (originCube d m) sOrder FiniteLpExponent.two g) →
      ∀ y ∈ cube d m,
        truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y →
        translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
        ∀ uD : H1Function (translatedCube d (n - 2) y),
          (∀ q, uD.toFun q = u.toFun q) → (∀ q, uD.grad q = u.grad q) →
          ∀ (v : H1Function (translatedCube d (n - 2) y)),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v →
            HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD →
            normalizedL2On (truncatedCube d m (n - 4) x)
                (fun q => u.toFun q - v.toFun q) ≤
              C * s ^ (-3 / 2 : ℝ) * err.toReal *
                  normalizedL2On (truncatedCube d m n x)
                    (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
                C * s ^ (-15 / 2 : ℝ) * (a0)⁻¹ *
                  (3 : ℝ) ^ ((1 + s) * n) *
                  (fractionalSeminormOn (truncatedCube d m n x) s g).toReal) := by
  intro Cerr hCerr
  obtain ⟨K, hK, henergy⟩ := inputs_det_interior_energy d hd Cerr hCerr
  obtain ⟨C, hC, hmain⟩ :=
    SubdiffusiveProcess.InteriorComparisonEngine.aux_icc_interior_comparison
      d hd Cerr K hCerr hK
  refine ⟨C, hC, ?_⟩
  intro s hs hs1 m n hnm z hz x hx hbd a data a0 ha0 err herr u g hweak hgex y hy
    hcov hloc uD huval hugrad v hv htrace
  obtain ⟨dataY⟩ := aux_inputs_det_interior_comparison_dataY d a z y data
  exact hmain s hs hs1 m n hnm z x y hx a data dataY a0 ha0 herr u g hweak hgex hloc hcov
    uD huval
    (henergy s hs hs1 m n hnm z hz x hx a data a0 ha0 herr hbd u g hweak hgex y hy hloc dataY)
    v hv htrace

end SubdiffusiveProcess.Paper
