import Mathlib
import SubdiffusiveProcess.Paper.conv_represented_catalogue_hdata_buffered

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped Topology ENNReal NNReal ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The catalogue with buffered traces is in particular the catalogue without the extra requirement. -/
theorem aux_conv_represented_catalogue_hdata_orig_of_buffered (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))) (NE NF : ℕ → ℕ)
    (alpha eta : ℝ)
    (h : conv_represented_env_interface_buffered d hd model H z r hr Sspace NE NF alpha
      eta) :
    aux_conv_represented_env_interface_orig d hd model H z r hr Sspace NE NF alpha eta := by
  obtain ⟨cR, cC, root, hunit, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
    ucellE, ucellF, Cext, beta, t, I, cK, eK, lK, sRK, sGK, sHK, cRK, cGK, cHK, origin, gridRoot,
    gridKey, G0E, G0F, hrm, hrt, hbuf, hcores⟩ := h
  exact ⟨cR, cC, root, hunit, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
    ucellE, ucellF, Cext, beta, t, I, cK, eK, lK, sRK, sGK, sHK, cRK, cGK, cHK, origin, gridRoot,
    gridKey, G0E, G0F, hrm, hrt, hcores⟩

/-- **The per-`k` finite-cutoff catalogue of the expanding-catalogue theorem, for the actual model.**
Let `(Z i, R i)` be a countable family of rational-centred cubes with triadic sides containing every such
cube, with pinned killed response spaces.  With one threshold `δ0` chosen before the model and all cutoff
sequences, for every model with `δ ≤ δ0`, every strictly increasing `NE`, `NF` and every `k` there is an
enumeration `e` of catalogue cubes covering the first `k+1` cubes of the family such that the original-space
finite-cutoff catalogue `aux_conv_represented_env_interface_orig` holds for the family `Z ∘ e`. -/
theorem conv_represented_catalogue_hdata
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pin : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (alpha eta beta t : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (heta : 0 < eta) (hAeta : 1 + eta < 2 * alpha) (hb : 1 / 2 < beta) (hba : beta < alpha) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H),
        M.delta ≤ δ0 →
      ∀ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
        (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
        (hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (Z i) (R i) (hR i)))
        (hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m)
        (hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ), (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
          (∃ m : ℤ, r' = (3 : ℝ) ^ m) → ∃ i, Z i = z' ∧ R i = r')
        (NE NF : ℕ → ℕ), StrictMono NE → StrictMono NF →
      ∀ k : ℕ, ∃ e : ℕ → ℕ, (∀ i ≤ k, ∃ j, e j = i) ∧
        aux_conv_represented_env_interface_orig d hd M H (Z ∘ e) (R ∘ e)
          (fun j => hR (e j)) (fun j => Sspace (e j)) NE NF alpha eta := by
  obtain ⟨δ0, hδ0, hbuf⟩ := conv_represented_catalogue_hdata_buffered d hd E Pin X W Cp Sob alpha
    eta beta t ht htd ha0 ha1 heta hAeta hb hba
  refine ⟨δ0, hδ0, ?_⟩
  intro M Rm Sreg It H hH hδ Z R hR Sspace hS hrat hcomp NE NF hNE hNF k
  obtain ⟨e, hk, hcat⟩ := hbuf M Rm Sreg It H hH hδ Z R hR Sspace hS hrat hcomp NE NF hNE hNF k
  exact ⟨e, hk, aux_conv_represented_catalogue_hdata_orig_of_buffered d hd M H (Z ∘ e) (R ∘ e)
    (fun j => hR (e j)) (fun j => Sspace (e j)) NE NF alpha eta hcat⟩

end Paper
