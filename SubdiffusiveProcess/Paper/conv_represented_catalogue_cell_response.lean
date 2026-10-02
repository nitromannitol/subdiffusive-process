import Mathlib
import SubdiffusiveProcess.Lnorm.CutoffVolumeResponseMeasurability
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Sobolev.NativeBoundaryResponse
import SubdiffusiveProcess.Sobolev.PotentialResponses
import SubdiffusiveProcess.Sobolev.BoundaryGrowthEnergy
import SubdiffusiveProcess.FiniteStopping.CutoffRestrictions
import SubdiffusiveProcess.Lane2.BoundaryResponse

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped Topology ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem aux_conv_represented_cell_response_eq_potential
    (d : ℕ) [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (e : H1Function (centeredCube z r hr : Set (SpatialCoordinates d))) (N : ℕ) (β : BilateralField d) :
    cellDirichletInfimum (cutoffCoefficient M H β N) (centeredCube z r hr : Set (SpatialCoordinates d)) e =
      dirichletResponse (killedResponseSpace (centeredCube_killedPoincare z hr))
        (expPotentialCoefficient (Lnorm.proxy_pot (H β) M N β z r hr))
        ⟨sobolevDataOfH1 e, sobolevDataOfH1_mem_weak e⟩ := by
  rw [← Lnorm.proxy_pot_eq_coefficient]
  exact cellDirichletInfimum_eq_dirichletResponse (centeredCube_killedPoincare z hr)
    (Lane4.cutoffPositiveCoefficient M H β N z hr) (cutoffCoefficient M H β N)
    (FiniteStopping.cutoffCoefficient_ae M H β N z hr) e

/-- **Cell responses of the catalogue: measurability, nonnegativity and tightness.**  For a native
`H¹` datum `e` on a cube, the boundary response `Λ_N(β)(e) = cellDirichletInfimum (A_N(β)) Q e` of the
actual finite-cutoff coefficient is measurable in the environment for every `N` and nonnegative.  If it is
dominated on an event `G` of full measure by a constant multiple of a family `Kext` (the absolute trace
estimate `eq:mfd-2` for this datum, with `c = Cext · r^{d-2} · ‖e‖²_{C^β/ℝ}`) that is bounded in probability
along a cutoff sequence `Ns`, then the responses along `Ns` are bounded in probability. -/
theorem conv_represented_catalogue_cell_response
    (d : ℕ) (hd : 0 < d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (e : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (Kext : ℕ → BilateralField d → ℝ) (G : Set (BilateralField d))
    (c : ℝ) (hc : 0 ≤ c)
    (hI : ∀ N, ∀ β ∈ G,
      cellDirichletInfimum (cutoffCoefficient M H β N)
        (centeredCube z r hr : Set (SpatialCoordinates d)) e ≤ c * Kext N β)
    (P0 : Measure (BilateralField d)) (hG : P0 Gᶜ = 0) (Ns : ℕ → ℕ)
    (hKtight : ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      P0 {β | Mb < Kext (Ns n) β} ≤ ENNReal.ofReal rho) :
    (∀ N, Measurable (fun β => cellDirichletInfimum (cutoffCoefficient M H β N)
      (centeredCube z r hr : Set (SpatialCoordinates d)) e)) ∧
    (∀ N β, 0 ≤ cellDirichletInfimum (cutoffCoefficient M H β N)
      (centeredCube z r hr : Set (SpatialCoordinates d)) e) ∧
    (∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      P0 {β | Mb < |cellDirichletInfimum (cutoffCoefficient M H (β) (Ns n))
        (centeredCube z r hr : Set (SpatialCoordinates d)) e|} ≤ ENNReal.ofReal rho) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hnn : ∀ N β, 0 ≤ cellDirichletInfimum (cutoffCoefficient M H β N)
      (centeredCube z r hr : Set (SpatialCoordinates d)) e := fun N β => by
    rw [aux_conv_represented_cell_response_eq_potential d M H z r hr e N β]
    exact dirichletResponse_nonneg _ _ _
  refine ⟨fun N => ?_, hnn, ?_⟩
  · letI : MeasurableSpace (Lp ℝ ∞ (volume.restrict
        ((centeredCube z r hr : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)))) := borel _
    haveI : BorelSpace (Lp ℝ ∞ (volume.restrict
        ((centeredCube z r hr : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)))) := ⟨rfl⟩
    have hsm := (continuous_dirichletResponse_potential
        (killedResponseSpace (centeredCube_killedPoincare z hr))
        ⟨sobolevDataOfH1 e, sobolevDataOfH1_mem_weak e⟩).comp_stronglyMeasurable
      (Lnorm.stronglyMeasurable_cutoffPotential_Lp M H hH.1 N z r hr)
    have hfun : (fun β => cellDirichletInfimum (cutoffCoefficient M H β N)
        (centeredCube z r hr : Set (SpatialCoordinates d)) e) =
        fun β => dirichletResponse (killedResponseSpace (centeredCube_killedPoincare z hr))
          (expPotentialCoefficient (Lnorm.proxy_pot (H β) M N β z r hr))
          ⟨sobolevDataOfH1 e, sobolevDataOfH1_mem_weak e⟩ :=
      funext fun β => aux_conv_represented_cell_response_eq_potential d M H z r hr e N β
    rw [hfun]
    exact hsm.measurable
  · intro rho hrho
    obtain ⟨Mb, hMb⟩ := hKtight rho hrho
    refine ⟨c * Mb, fun n => ?_⟩
    have hsub : {β | c * Mb < |cellDirichletInfimum (cutoffCoefficient M H β (Ns n))
        (centeredCube z r hr : Set (SpatialCoordinates d)) e|} ⊆
        {β | Mb < Kext (Ns n) β} ∪ Gᶜ := by
      intro β hβ
      by_cases hβG : β ∈ G
      · left
        rw [Set.mem_setOf_eq, abs_of_nonneg (hnn (Ns n) β)] at hβ
        have hlt : c * Mb < c * Kext (Ns n) β := lt_of_lt_of_le hβ (hI (Ns n) β hβG)
        exact lt_of_mul_lt_mul_left hlt hc
      · exact Or.inr hβG
    calc P0 _ ≤ P0 ({β | Mb < Kext (Ns n) β} ∪ Gᶜ) := measure_mono hsub
      _ ≤ P0 {β | Mb < Kext (Ns n) β} + P0 Gᶜ := measure_union_le _ _
      _ ≤ ENNReal.ofReal rho := by rw [hG, add_zero]; exact hMb n

end Paper
