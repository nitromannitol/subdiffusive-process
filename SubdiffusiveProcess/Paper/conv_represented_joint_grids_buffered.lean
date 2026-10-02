import SubdiffusiveProcess.Paper.conv_represented_joint_grids
import SubdiffusiveProcess.Paper.conv_represented_joint_buffered
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem conv_represented_joint_grids_buffered (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d) (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ) (E : Paper.in_J d) (beta0 t0 : ℝ)
    (h : conv_represented_joint_grids d hd model H Ω P field envE envF z r hr Sspace
      GNE GNF GE GF NE NF alpha eta E beta0 t0) :
    conv_represented_joint_buffered d hd model H Ω P field envE envF z r hr Sspace
      GNE GNF GE GF NE NF alpha eta := by
  refine ⟨h.1, ?_⟩
  intro k
  obtain ⟨e, he, cat⟩ := h.2 k
  obtain ⟨cR, cC, respE, respF, eventE, eventF, root, hunit, Dcat, hDcat,
    fcat, trace, traceH1, usrcE, usrcF, srcE, srcF, ucellE, ucellF,
    Cext, beta, t, I, cK, eK, lK, sRK, sGK, sHK, cRK, cGK, cHK,
    origin, gridRoot, gridKey, hAnchor, hgrid, hbuf, hrep⟩ := cat
  exact ⟨e, he, cR, cC, respE, respF, eventE, eventF, root, hunit, Dcat, hDcat,
    fcat, trace, traceH1, usrcE, usrcF, srcE, srcF, ucellE, ucellF,
    Cext, beta, t, I, cK, eK, lK, sRK, sGK, sHK, cRK, cGK, cHK,
    origin, gridRoot, gridKey, hbuf, hrep⟩
end Paper
