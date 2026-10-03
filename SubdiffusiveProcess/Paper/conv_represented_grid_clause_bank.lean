module

public import SubdiffusiveProcess.Paper.model_grid_constant_bank

@[expose] public section




open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- **Clause J of the represented catalogue from the whole-grid constant bank.** -/
theorem conv_represented_grid_clause_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Xc : in_extension d hd E)
    (Sf : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (eta p beta : ℝ) (heta : 0 < eta) (hp : 1 ≤ p) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ δ0 →
      ∀ (J : Type) [Countable J] (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j)
        (Grid : Type) [Countable Grid] (origin : Grid → SpatialCoordinates d)
        (gridRoot : Grid → J),
      ∃ (Zg : Grid → ℕ → BilateralField d → ℝ) (Cb : Grid → ℝ) (Ggrid : Set (BilateralField d)),
        (∀ g, 0 ≤ Cb g) ∧
        (∀ g N, Measurable (Zg g N)) ∧
        (∀ g N β, 0 ≤ Zg g N β) ∧
        (∀ g N, ∀ q : ℝ, 0 < q → q ≤ p →
          MemLp (Zg g N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (Zg g N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cb g)) ∧
        (∀ g, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ N,
          (chaosSampleLaw M).toMeasure {β | Mb < Zg g N β} ≤ ENNReal.ofReal rho) ∧
        MeasurableSet Ggrid ∧ (chaosSampleLaw M).toMeasure Ggridᶜ = 0 ∧
        ∀ (Index : Type) (constants : Index → ℕ → BilateralField d → ℝ)
          (extensionKey lambdaKey : J → Index) (gridKey : Grid → Index) (cutoff : ℕ → ℕ)
          (G0 : Set (BilateralField d)),
          (∀ (j : J) (n : ℕ) (β : BilateralField d), β ∈ G0 →
            constants (extensionKey j) n β =
              E.Lam (z j) (r j) (hr j)
                (cutoffPositiveCoefficient M H β (cutoff n) (z j) (hr j))
                (z j) (r j) ((beta - 1 / 2) / 4) 2 ∧
            constants (lambdaKey j) n β =
              (E.lam (z j) (r j) (hr j)
                (cutoffPositiveCoefficient M H β (cutoff n) (z j) (hr j))
                (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ))) →
          (∀ (g : Grid) (n : ℕ) (β : BilateralField d), β ∈ G0 →
            constants (gridKey g) n β = Zg g (cutoff n) β) →
          ∀ (g : Grid) (n k : ℕ) (j : J) (β : BilateralField d), β ∈ G0 → β ∈ Ggrid →
            k ≤ cutoff n → r j = (3 : ℝ) ^ (-(k : ℤ)) →
            (∃ idx : Fin d → ℤ,
              z j = (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * (idx i : ℝ))) →
            (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ⊆
              (centeredCube (z (gridRoot g)) (r (gridRoot g)) (hr (gridRoot g)) :
                Set (SpatialCoordinates d)) →
            constants (extensionKey j) n β + constants (lambdaKey j) n β ≤
              constants (gridKey g) n β * (r j) ^ (-eta)
  := by
  obtain ⟨δ0, hδ0, hbank⟩ := model_grid_constant_bank d hd E Xc Sf eta p beta heta hp hbeta
  refine ⟨δ0, hδ0, ?_⟩
  intro M Rm H hH hδ J _ z r hr Grid _ origin gridRoot
  obtain ⟨Zg, Cb, Ggrid, hCb, hmeas, hnn, hmom, htight, hGm, hG0, hmain⟩ :=
    hbank M Rm H hH hδ Grid (fun g => z (gridRoot g)) (fun g => r (gridRoot g))
      (fun g => hr (gridRoot g)) origin
  refine ⟨Zg, Cb, Ggrid, hCb, hmeas, hnn, hmom, htight, hGm, hG0, ?_⟩
  intro Index constants extensionKey lambdaKey gridKey cutoff G0 hpin hgrid g n k j β hβ0 hβg hk
    hrj hzj hsub
  obtain ⟨idx, hidx⟩ := hzj
  obtain ⟨he, hl⟩ := hpin j n β hβ0
  rw [he, hl, hgrid g n β hβ0, Real.rpow_neg_one]
  have hpos : 0 < (3 : ℝ) ^ (-(k : ℤ)) := by positivity
  have key : ∀ (w : SpatialCoordinates d) (s : ℝ) (hs : 0 < s),
      w = (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * (idx i : ℝ)) → s = (3 : ℝ) ^ (-(k : ℤ)) →
      (centeredCube w s hs : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z (gridRoot g)) (r (gridRoot g)) (hr (gridRoot g)) :
          Set (SpatialCoordinates d)) →
      E.Lam w s hs (cutoffPositiveCoefficient M H β (cutoff n) w hs) w s ((beta - 1 / 2) / 4) 2 +
        (E.lam w s hs (cutoffPositiveCoefficient M H β (cutoff n) w hs) w s
          ((beta - 1 / 2) / 4) 2)⁻¹ ≤ Zg g (cutoff n) β * s ^ (-eta) := by
    intro w s hs hw hs' hsub'
    subst hw
    subst hs'
    exact hmain β hβg g (cutoff n) k idx hk hs hsub'
  exact key (z j) (r j) (hr j) hidx hrj hsub

end Paper
