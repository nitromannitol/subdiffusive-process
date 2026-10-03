module

public import SubdiffusiveProcess.Paper.goodext_represented_controls_with_bank
public import SubdiffusiveProcess.Paper.goodext_represented_cell_growth_bank
public import SubdiffusiveProcess.Paper.goodext_represented_grid_coefficient_bank
public import SubdiffusiveProcess.Sobolev.HarmonicSmoothGrowth

@[expose] public section

/-! Establishes ambient controls, all-level shifted-grid coefficient bounds, and smooth-data
minimizer regularity on one represented subsequence. The coefficient conclusion is only asserted
for levels eventually below the supplied cutoff. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace Paper

/-- A single represented subsequence retains ambient controls and smooth-minimizer regularity and upper coefficients on a countable triadic-cell catalogue. -/
theorem goodext_represented_grid_trace_controls
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd)
    (t alpha beta etaGrid : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hb : beta ∈ Ioo (1 / 2 : ℝ) 1) (hetaGrid : 0 < etaGrid) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
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
      ∀ᵐ om ∂P,
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S
          (fun n => cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) z hr)) ∧
        aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
          (fun n => cutoffCoefficient M H (env (seq n) om) (N (seq n))) t alpha ∧
        ∃ K : ℝ, 0 ≤ K ∧ ∀ (k : ℕ) (j : Fin J) (idx : Fin d → ℤ),
          let wc : SpatialCoordinates d := fun i => origins j i + (3 : ℝ) ^ (-(k : ℤ)) * idx i
          let rc : ℝ := (3 : ℝ) ^ (-(k : ℤ))
          ∀ hc : 0 < rc,
          (centeredCube wc rc hc : Set (SpatialCoordinates d)) ⊆
            (centeredCube z r hr : Set (SpatialCoordinates d)) →
          (∀ᶠ n in atTop, I.Lam wc rc hc
            (cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) wc hc)
            wc rc ((beta - 1 / 2) / 4) 2 ≤ K * rc ^ (-etaGrid)) ∧
          ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
          ∀ b : weakSobolevGraph (centeredCube wc rc hc),
            ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (centeredCube wc rc hc : Set (SpatialCoordinates d))] phi) →
            ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∃ V : SpatialCoordinates d → ℝ,
              ContinuousOn V (closure (centeredCube wc rc hc : Set (SpatialCoordinates d))) ∧
              ((dirichletMinimizer
                (killedResponseSpace (centeredCube_killedPoincare wc hc))
                (cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) wc hc) b).val.1 :
                  SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                    (centeredCube wc rc hc : Set (SpatialCoordinates d))] V ∧
              IsHolderOn alpha (closure
                (centeredCube wc rc hc : Set (SpatialCoordinates d))) V ∧
              cAlphaNorm alpha (closure
                (centeredCube wc rc hc : Set (SpatialCoordinates d))) V ≤ C := by
  classical
  obtain ⟨deltaGrowth, hdeltaGrowth, hGrowthAll⟩ :=
    goodext_represented_cell_growth_bank d hd I Pin X W Cp Sob t alpha
      ht htd ha ha1
  obtain ⟨deltaGrid, hdeltaGrid, hGridAll⟩ :=
    goodext_represented_grid_coefficient_bank d hd I X Sob beta etaGrid hb hetaGrid
  obtain ⟨deltaControls, hdeltaControls, hControlsAll⟩ :=
    goodext_represented_controls_with_bank d hd I Pin X W Cp Sob Interp t alpha
      ht htd ha ha1
  refine ⟨min deltaControls (min deltaGrowth deltaGrid),
    lt_min hdeltaControls (lt_min hdeltaGrowth hdeltaGrid), ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr S hS J origins N hN Omega _ P _ env hEnv hLaw
  let CellIndex := ℕ × (Fin J × (Fin d → ℤ))
  letI cellCountable : Countable CellIndex := by infer_instance
  letI combinedCountable : Countable (CellIndex ⊕ PUnit) := by infer_instance
  let center : CellIndex → SpatialCoordinates d := fun c i =>
    origins c.2.1 i + (3 : ℝ) ^ (-(c.1 : ℤ)) * c.2.2 i
  let radius : CellIndex → ℝ := fun c => (3 : ℝ) ^ (-(c.1 : ℤ))
  have hradius : ∀ c, 0 < radius c := by
    intro c
    dsimp only [radius]
    exact zpow_pos (by norm_num : (0 : ℝ) < 3) _
  have hdeltaControls' : M.delta ≤ deltaControls :=
    hdelta.trans (min_le_left _ _)
  have hdeltaGrowth' : M.delta ≤ deltaGrowth :=
    hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaGrid' : M.delta ≤ deltaGrid :=
    hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨growthBank, growthBounds, hgrowthMem, hgrowthNorm, hgrowthAll⟩ :=
    hGrowthAll M Rm Sreg It H hIR hdeltaGrowth' CellIndex center radius hradius N
      Omega P env hEnv hLaw
  obtain ⟨gridBank, gridBound, hgridMem, hgridNorm, hgridAll⟩ :=
    hGridAll M Rm H hIR hdeltaGrid' z r hr J origins N Omega P env hEnv hLaw
  let combinedBank : CellIndex ⊕ PUnit → ℕ → Omega → ℝ := fun q n om =>
    match q with
    | Sum.inl c => growthBank c n om
    | Sum.inr _ => gridBank n om
  let combinedBounds : CellIndex ⊕ PUnit → ℝ≥0 := fun q =>
    match q with
    | Sum.inl c => growthBounds c
    | Sum.inr _ => gridBound
  have hcombinedMem : ∀ q n, MemLp (combinedBank q n) 1 P := by
    intro q n
    cases q with
    | inl c => exact hgrowthMem c n
    | inr _ => exact hgridMem n
  have hcombinedNorm : ∀ q n, eLpNorm (combinedBank q n) 1 P ≤ combinedBounds q := by
    intro q n
    cases q with
    | inl c => exact hgrowthNorm c n
    | inr _ => exact hgridNorm n
  have hControls := hControlsAll M Rm Sreg It H hIR hdeltaControls' z r hr S hS N
    Omega P env hEnv hLaw (CellIndex ⊕ PUnit) combinedBank combinedBounds
    hcombinedMem hcombinedNorm
  filter_upwards [hControls, hgrowthAll, hgridAll] with om hControlsOm hgrowthOm hgridOm
  obtain ⟨seq, hseq, hAmbient, hAllCell, hCaps⟩ := hControlsOm
  obtain ⟨K, hK, hGridCapRaw⟩ := hCaps (Sum.inr PUnit.unit)
  have hGridCap : ∀ n, |gridBank (seq n) om| ≤ K := by
    intro n
    simpa only [combinedBank] using hGridCapRaw n
  refine ⟨seq, hseq, hAmbient, hAllCell, ⟨K, hK, ?_⟩⟩
  intro k j idx wc rc hc hsub
  constructor
  · have hlevel : ∀ᶠ n in atTop, k ≤ N (seq n) := by
      refine Filter.eventually_atTop.2 ⟨k, ?_⟩
      intro n hkn
      exact (hkn.trans (hseq.id_le n)).trans (hN.id_le (seq n))
    have hfactor : 0 ≤ rc ^ (-etaGrid) := Real.rpow_nonneg hc.le _
    filter_upwards [hlevel] with n hn
    have hcoefficient := hgridOm (seq n) k j idx hn hc hsub
    have hinv : 0 ≤ (I.lam wc rc hc
        (cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) wc hc)
        wc rc ((beta - 1 / 2) / 4) 2)⁻¹ :=
      inv_nonneg.mpr (I.lam_pos wc rc hc
        (cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) wc hc)
        wc rc ((beta - 1 / 2) / 4) 2).le
    calc
      I.Lam wc rc hc
          (cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) wc hc)
          wc rc ((beta - 1 / 2) / 4) 2 ≤
          I.Lam wc rc hc
            (cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) wc hc)
            wc rc ((beta - 1 / 2) / 4) 2 +
              (I.lam wc rc hc
                (cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) wc hc)
                wc rc ((beta - 1 / 2) / 4) 2)⁻¹ :=
        le_add_of_nonneg_right hinv
      _ ≤ gridBank (seq n) om * rc ^ (-etaGrid) := hcoefficient
      _ ≤ K * rc ^ (-etaGrid) :=
        mul_le_mul_of_nonneg_right
          ((le_abs_self _).trans (hGridCap n)) hfactor
  · intro phi hphi b hb
    let cell : CellIndex := (k, (j, idx))
    obtain ⟨Kgrowth, hKgrowth, hGrowthCapRaw⟩ := hCaps (Sum.inl cell)
    have hGrowthCap : ∀ n, |growthBank cell (seq n) om| ≤ Kgrowth := by
      intro n
      simpa only [combinedBank] using hGrowthCapRaw n
    have hGrowthUniform : ∀ n (psi : SpatialCoordinates d → ℝ) (Cpsi : ℝ),
        ContDiff ℝ 2 psi → c2Norm (closedCube wc rc hc) psi ≤ Cpsi →
        ∀ b' u' : weakSobolevGraph (centeredCube wc rc hc),
          ((b'.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube wc rc hc : Set (SpatialCoordinates d))] psi) →
          SolvesDirichlet
            (cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) wc hc)
            (fun _ => 0) b' u' →
          ∃ V : SpatialCoordinates d → ℝ, Continuous V ∧
            ((u'.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (centeredCube wc rc hc : Set (SpatialCoordinates d))] V) ∧
            IsHolderOn alpha (closure
              (centeredCube wc rc hc : Set (SpatialCoordinates d))) V ∧
            cAlphaNorm alpha (closure
              (centeredCube wc rc hc : Set (SpatialCoordinates d))) V ≤ Kgrowth * Cpsi := by
      intro n psi Cpsi hpsi hCpsi b' u' hb' hu'
      have hpsi2 : ContDiff ℝ 2 psi := hpsi
      obtain ⟨V, hVcont, hVae, hVholder, hVnorm⟩ :=
        hgrowthOm cell (seq n) psi Cpsi hpsi2 hCpsi b' u' hb' hu'
      have hCpsi0 : 0 ≤ Cpsi :=
        (aux_prop_growth_c2Norm_nonneg _ _).trans hCpsi
      have hbankBound : growthBank cell (seq n) om ≤ Kgrowth :=
        (le_abs_self _).trans (hGrowthCap n)
      refine ⟨V, hVcont, hVae, hVholder, ?_⟩
      exact hVnorm.trans (mul_le_mul_of_nonneg_right hbankBound hCpsi0)
    exact smooth_minimizer_regularity_of_growth wc rc hc
      (centeredCube_killedPoincare wc hc)
      (fun n => cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) wc hc)
      alpha Kgrowth hKgrowth hGrowthUniform phi hphi b hb
