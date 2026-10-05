module

public import Mathlib
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_original_grids
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_geometry
public import SubdiffusiveProcess.Paper.conv_represented_env_interface_grids

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **The per-`k` finite-cutoff catalogue of the expanding-catalogue theorem, for the actual model.**
Let `(Z i, R i)` be a countable family of rational-centred cubes with triadic sides containing every such
cube, with pinned killed response spaces.  With one threshold `δ0` chosen before the model and all cutoff
sequences, for every model with `δ ≤ δ0`, every strictly increasing `NE`, `NF` and every `k` there is an
enumeration `e` of catalogue cubes covering the first `k+1` cubes of the family such that the original-space
finite-cutoff catalogue with the buffered collar profiles as traces
(`conv_represented_env_interface_grids`) holds for the family `Z ∘ e`. -/
theorem conv_represented_catalogue_hdata_grids
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pin : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (alpha eta beta t : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (heta : 0 < eta) (hAeta : 1 + eta < 2 * alpha) (hb : 1 / 2 < beta) (hba : beta < alpha) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ δ0 →
      ∀ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
        (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
        (_hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (Z i) (R i) (hR i)))
        (_hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m)
        (_hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ), (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
          (∃ m : ℤ, r' = (3 : ℝ) ^ m) → ∃ i, Z i = z' ∧ R i = r')
        (NE NF : ℕ → ℕ), StrictMono NE → StrictMono NF →
      ∀ k : ℕ, ∃ e : ℕ → ℕ, (∀ i ≤ k, ∃ j, e j = i) ∧
        conv_represented_env_interface_grids d hd M H (Z ∘ e) (R ∘ e)
          (fun j => hR (e j)) (fun j => Sspace (e j)) NE NF alpha eta E beta t := by
  obtain ⟨δ0, hδ0, horig⟩ := conv_represented_catalogue_original_grids d hd E Pin X W Cp Sob alpha eta
    beta t ht htd ha0 ha1 heta hAeta hb hba
  refine ⟨δ0, hδ0, ?_⟩
  intro M Rm Sreg It H hH hδ Z R hR Sspace hS hrat hcomp NE NF hNE hNF k
  obtain ⟨e, root, origin, gridRoot, hk, hunit, hsub, hrat', htri, hcomp', horat, hgrid⟩ :=
    conv_represented_catalogue_geometry d Z R hR hrat hcomp k
  exact ⟨e, hk, horig M Rm Sreg It H hH hδ (Z ∘ e) (R ∘ e) (fun j => hR (e j))
    (fun j => Sspace (e j)) (fun j => hS (e j)) root origin gridRoot hunit hsub hrat' htri hcomp'
    horat hgrid NE NF hNE hNF⟩

end SubdiffusiveProcess.Paper
