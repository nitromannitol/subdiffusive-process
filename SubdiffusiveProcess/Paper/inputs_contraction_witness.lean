module

public import SubdiffusiveProcess.Paper.inputs_contraction_graph
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem inputs_contraction_witness (d : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ)
    (hT : _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T) (u : S.space) :
    ∃ v : S.space,
      ((v.val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
          (fun x => T (u.val.1 x))) ∧
      responseForm S a v v ≤ responseForm S a u u := by
  let Ω : Opens (SpatialCoordinates d) := centeredCube z r hr
  let uGraph : killedSobolevGraph Ω :=
    ⟨u.val, by rw [← hS]; exact u.property⟩
  obtain ⟨vGraph, theta, htheta, hvalue, hgradient⟩ :=
    inputs_contraction_graph d Ω uGraph T hT
  let v : S.space := ⟨vGraph.val, by rw [hS]; exact vGraph.property⟩
  have hgradient' :
      (fun x i => v.val.2 i x) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        fun x => theta x • (fun i => u.val.2 i x) := by
    simpa [v, uGraph] using hgradient
  have hgradient_point :
      ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
        ∀ i, v.val.2 i x = theta x * u.val.2 i x := by
    filter_upwards [hgradient'] with x hx
    intro i
    simpa using congrFun hx i
  have ha_nonneg := SubdiffusiveProcess.positiveCoefficient_ae_nonneg a
  have hterm (i : Fin d) :
      ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
        a.val x * (v.val.2 i x * v.val.2 i x) ≤
          a.val x * (u.val.2 i x * u.val.2 i x) := by
    filter_upwards [ha_nonneg, hgradient_point] with x ha hgrad
    have htheta_sq : theta x ^ 2 ≤ 1 := by
      have habs := abs_le.mp (htheta x)
      nlinarith [sq_nonneg (theta x)]
    have hsq :
        (theta x * u.val.2 i x) * (theta x * u.val.2 i x) ≤
          u.val.2 i x * u.val.2 i x := by
      calc
        (theta x * u.val.2 i x) * (theta x * u.val.2 i x) =
            theta x ^ 2 * (u.val.2 i x ^ 2) := by ring
        _ ≤ 1 * (u.val.2 i x ^ 2) :=
          mul_le_mul_of_nonneg_right htheta_sq (sq_nonneg _)
        _ = u.val.2 i x * u.val.2 i x := by ring
    calc
      a.val x * (v.val.2 i x * v.val.2 i x) =
          a.val x * ((theta x * u.val.2 i x) * (theta x * u.val.2 i x)) := by
            rw [hgrad i]
      _ ≤ a.val x * (u.val.2 i x * u.val.2 i x) :=
        mul_le_mul_of_nonneg_left hsq ha
  refine ⟨v, ?_, ?_⟩
  · simpa [v, uGraph, Ω] using hvalue
  · rw [responseForm_apply, responseForm_apply]
    apply Finset.sum_le_sum
    intro i hi
    apply integral_mono_ae
    · simpa only [RCLike.inner_apply, conj_trivial] using
        SubdiffusiveProcess.integrable_weighted_inner
          (μ := volume.restrict (Ω : Set (SpatialCoordinates d)))
          a.val (v.val.2 i) (v.val.2 i)
    · simpa only [RCLike.inner_apply, conj_trivial] using
        SubdiffusiveProcess.integrable_weighted_inner
          (μ := volume.restrict (Ω : Set (SpatialCoordinates d)))
          a.val (u.val.2 i) (u.val.2 i)
    · exact hterm i

end SubdiffusiveProcess.Paper

