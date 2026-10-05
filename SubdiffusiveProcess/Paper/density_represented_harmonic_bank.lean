module

public import SubdiffusiveProcess.Paper.density_harmonic_energy_bank
public import SubdiffusiveProcess.Paper.goodext_represented_grid_trace_controls
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper
/-- Actual represented grid controls construct the countable harmonic energy bank
for every fixed Holder boundary datum. Ambient controls are retained; all energy
limits belong to the actual finite-cutoff minimizers on the displayed refinement. -/
theorem density_represented_harmonic_bank
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd)
    (t alpha beta etaGrid : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hba : beta ≤ alpha) (hb : beta ∈ Ioo (1 / 2 : ℝ) 1) (hetaGrid : 0 < etaGrid) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr))
        (hS : S.space = killedSobolevGraph (centeredCube z r hr))
        (J : ℕ) (origins : Fin J → SpatialCoordinates d)
        (N : ℕ → ℕ) (hN : StrictMono N)
        (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
        (env : ℕ → Omega → BilateralField d)
        (hEnv : ∀ n, Measurable (env n))
        (hLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure),
      ∀ (Cells : Type) [Countable Cells] (level : Cells → ℕ)
        (cellOrigin : Cells → Fin J) (idx : Cells → Fin d → ℤ),
      let centre := fun q i => origins (cellOrigin q) i + (3 : ℝ) ^ (-(level q : ℤ)) * idx q i
      let radius := fun q => (3 : ℝ) ^ (-(level q : ℤ))
      ∀ hsub : ∀ q, (centeredCube (centre q) (radius q) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆
          (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ᵐ om ∂P,
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S
          (fun n => cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) z hr)) ∧
        aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
          (fun n => cutoffCoefficient M H (env (seq n) om) (N (seq n))) t alpha ∧
        ∀ g : SpatialCoordinates d → ℝ,
          ContinuousOn g (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
          IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) g →
    ∃ A0 Osc : ℝ, 0 ≤ A0 ∧ 0 ≤ Osc ∧
      ∃ (datum : ∀ q, weakSobolevGraph (centeredCube (centre q) (radius q) (zpow_pos (by norm_num) _)))
        (VN : Cells → ℕ → SpatialCoordinates d → ℝ)
        (rho : ℕ → ℕ) (Vcell : Cells → SpatialCoordinates d → ℝ) (cost : Cells → ℝ),
      StrictMono rho ∧ ∀ q,
        (∀ n, ContinuousOn (VN q n)
            (closure (centeredCube (centre q) (radius q) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d))) ∧
          ((dirichletMinimizer (killedResponseSpace (centeredCube_killedPoincare (centre q) (zpow_pos (by norm_num) _)))
            (cutoffPositiveCoefficient M H (env (seq (rho n)) om) (N (seq (rho n)))
              (centre q) (zpow_pos (by norm_num) _)) (datum q)).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (centeredCube (centre q) (radius q) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d))] VN q n ∧
          (∀ x ∈ frontier (centeredCube (centre q) (radius q) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)),
            VN q n x = g x) ∧
          ∀ x ∈ closure (centeredCube (centre q) (radius q) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)),
            |VN q n x - g x| ≤ Osc * radius q ^ alpha) ∧
        ContinuousOn (Vcell q)
          (closure (centeredCube (centre q) (radius q) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d))) ∧
        TendstoUniformlyOn (VN q) (Vcell q) atTop
          (closure (centeredCube (centre q) (radius q) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d))) ∧
        Tendsto (fun n => dirichletResponse
          (killedResponseSpace (centeredCube_killedPoincare (centre q) (zpow_pos (by norm_num) _)))
          (cutoffPositiveCoefficient M H (env (seq (rho n)) om) (N (seq (rho n)))
              (centre q) (zpow_pos (by norm_num) _)) (datum q)) atTop (𝓝 (cost q)) ∧
        0 ≤ cost q ∧ cost q ≤ A0 * radius q ^ ((d : ℝ) - 2 + 2 * alpha - etaGrid) := by
  obtain ⟨delta0, hd0, hControls⟩ := goodext_represented_grid_trace_controls d hd I Pin X W Cp
    Sob Interp t alpha beta etaGrid ht htd ha ha1 hb hetaGrid
  refine ⟨delta0, hd0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr S hS J origins N hN Omega _ P _ env hEnv hLaw
    Cells _ level cellOrigin idx centre radius hsub
  have hAll := hControls M Rm Sreg It H hIR hdelta z r hr S hS J origins N hN
    Omega P env hEnv hLaw
  filter_upwards [hAll] with om h
  obtain ⟨seq, hseq, hAmbient, hCell, K, hK, hGrid⟩ := h
  refine ⟨seq, hseq, hAmbient, hCell, ?_⟩
  intro g hgc hgh
  have hRadius : ∀ q, 0 < radius q := fun q => zpow_pos (by norm_num) _
  have hSide : ∀ q, radius q ≤ 1 := fun q =>
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)
  let bcell := fun q n => cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n))
    (centre q) (hRadius q)
  have hrep : ∀ q n, (bcell q n).val =ᵐ[volume.restrict
      (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))]
        cutoffCoefficient M H (env (seq n) om) (N (seq n)) := fun q n =>
    (cutoffPositiveCoefficient_representative M H (env (seq n) om) (N (seq n))
      (centre q) (hRadius q)).2.2.2
  have hell : ∀ n, ∃ lo hi : ℝ, 0 < lo ∧
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        lo ≤ cutoffCoefficient M H (env (seq n) om) (N (seq n)) x ∧
        cutoffCoefficient M H (env (seq n) om) (N (seq n)) x ≤ hi := by
    intro n
    obtain ⟨lo, hi, hlo, hbound⟩ := cutoffCoefficient_closedCube_bounds M H
      (env (seq n) om) (N (seq n)) z hr
    exact ⟨lo, hi, hlo, fun x hx => hbound x (centeredCube_subset_closedCube z hr hx)⟩
  exact density_harmonic_energy_bank hd I X Sob z r hr Cells centre radius hRadius hSide hsub
    (fun n => cutoffCoefficient M H (env (seq n) om) (N (seq n)))
    (fun n => cutoffCoefficient_continuous M H (env (seq n) om) (N (seq n))) hell
    alpha beta etaGrid K ha hb hba hK g hgc hgh bcell hrep
    (fun q => (hGrid (level q) (cellOrigin q) (idx q) (hRadius q) (hsub q)).2)
    (fun q => (hGrid (level q) (cellOrigin q) (idx q) (hRadius q) (hsub q)).1)
end SubdiffusiveProcess.Paper
