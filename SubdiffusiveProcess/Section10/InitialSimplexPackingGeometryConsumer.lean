module

public import SubdiffusiveProcess.Section10.InitialSimplexPackingVolume
public import SubdiffusiveProcess.Section10.InitialSimplexPackingGeometryFacets
public import SubdiffusiveProcess.Section10.InitialSimplexEnergyStationarity

@[expose] public section




namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn

noncomputable section

/-- All packing premises in the existing energy supplier are discharged by
the finite geometric construction. No analytic argument is added here. -/
theorem exists_initialSimplexEnergy_all_cells_of_geometry (d : ℕ) (hd : 2 ≤ d) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∀ (ell : ℕ) (T : KuhnCell d), T.supportCube.scale = (ell : ℤ) → ∀ p : Vec d,
        (∫ omega, vecDot p (matVecMul
          (randomAMatrix M ell (kuhnCellDomain T) omega) p) ∂M.P.toMeasure) ≤
          C * ahom M ell * vecNormSq p := by
  obtain ⟨K, hK, hpack⟩ := exists_initialSimplexCubePacking d hd
  obtain ⟨delta0, C, hdelta0, hC, henergy⟩ :=
    exists_initialSimplexEnergy_all_cells_of_packing d K hK
  exact ⟨delta0, C, hdelta0, hC, fun M hM ell T hT p =>
    henergy M hM ell (hpack ell) T hT p⟩












end
end SubdiffusiveProcess.Section10
