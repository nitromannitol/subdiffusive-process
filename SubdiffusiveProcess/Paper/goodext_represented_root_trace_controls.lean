module

public import SubdiffusiveProcess.Paper.goodext_represented_controls_with_bank
public import SubdiffusiveProcess.Paper.goodext_represented_cell_growth_bank
public import SubdiffusiveProcess.Geometry.BoundaryPartitions
public import SubdiffusiveProcess.Sobolev.HarmonicSmoothGrowth

@[expose] public section




open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace Paper

/-- Root analytic controls and every root-grid smooth minimizer share one represented subsequence. -/
theorem goodext_represented_root_trace_controls
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd)
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr))
        (hS : S.space = killedSobolevGraph (centeredCube z r hr))
        (N : ℕ → ℕ)
        (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
        (env : ℕ → Omega → BilateralField d)
        (hEnv : ∀ n, Measurable (env n))
        (hLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure),
      ∀ᵐ om ∂P, ∃ seq : ℕ → ℕ, StrictMono seq ∧
        Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S
          (fun n => cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) z hr)) ∧
        aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
          (fun n => cutoffCoefficient M H (env (seq n) om) (N (seq n))) t alpha ∧
        ∀ q : TriadicGridLabel d,
          ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
          ∀ b : weakSobolevGraph (triadicGridCell z r hr q),
            ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (triadicGridCell z r hr q : Set (SpatialCoordinates d))] phi) →
            ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∃ V : SpatialCoordinates d → ℝ,
              ContinuousOn V (closure (triadicGridCell z r hr q : Set (SpatialCoordinates d))) ∧
              ((dirichletMinimizer
                (killedResponseSpace (centeredCube_killedPoincare (triadicGridCenter z r q)
                  (triadicGridSide_pos hr q)))
                (cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n))
                  (triadicGridCenter z r q) (triadicGridSide_pos hr q)) b).val.1 :
                    SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                      (triadicGridCell z r hr q : Set (SpatialCoordinates d))] V ∧
              IsHolderOn alpha (closure (triadicGridCell z r hr q : Set (SpatialCoordinates d))) V ∧
              cAlphaNorm alpha (closure (triadicGridCell z r hr q : Set (SpatialCoordinates d))) V ≤ C := by
  classical
  obtain ⟨deltaGrowth, hdeltaGrowth, hGrowthAll⟩ :=
    goodext_represented_cell_growth_bank d hd I Pin X W Cp Sob t alpha
      ht htd ha ha1
  obtain ⟨deltaControls, hdeltaControls, hControlsAll⟩ :=
    goodext_represented_controls_with_bank d hd I Pin X W Cp Sob Interp t alpha
      ht htd ha ha1
  refine ⟨min deltaControls deltaGrowth,
    lt_min hdeltaControls hdeltaGrowth, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr S hS N Omega _ P _ env hEnv hLaw
  have hdeltaControls' : M.delta ≤ deltaControls :=
    hdelta.trans (min_le_left _ _)
  have hdeltaGrowth' : M.delta ≤ deltaGrowth :=
    hdelta.trans (min_le_right _ _)
  letI rootLabelCountable : Countable (TriadicGridLabel d) := by
    unfold TriadicGridLabel
    infer_instance
  let rootCenter : TriadicGridLabel d → SpatialCoordinates d :=
    fun q => triadicGridCenter z r q
  let rootSide : TriadicGridLabel d → ℝ :=
    fun q => triadicGridSide r q
  have hrootSide : ∀ q, 0 < rootSide q := by
    intro q
    dsimp only [rootSide]
    exact triadicGridSide_pos hr q
  obtain ⟨growthBank, growthBounds, hgrowthMem, hgrowthNorm, hgrowthAll⟩ :=
    hGrowthAll M Rm Sreg It H hIR hdeltaGrowth'
      (TriadicGridLabel d) rootCenter rootSide hrootSide N Omega P env hEnv hLaw
  have hControls :=
    hControlsAll M Rm Sreg It H hIR hdeltaControls' z r hr S hS N
      Omega P env hEnv hLaw (TriadicGridLabel d) growthBank growthBounds
      hgrowthMem hgrowthNorm
  filter_upwards [hControls, hgrowthAll] with om hControlsOm hgrowthOm
  obtain ⟨seq, hseq, hAmbient, hAllCell, hCaps⟩ := hControlsOm
  refine ⟨seq, hseq, hAmbient, hAllCell, ?_⟩
  intro q phi hphi b hb
  obtain ⟨Kgrowth, hKgrowth, hGrowthCapRaw⟩ := hCaps q
  have hGrowthCap : ∀ n, |growthBank q (seq n) om| ≤ Kgrowth := by
    intro n
    exact hGrowthCapRaw n
  have hGrowthUniform : ∀ n (psi : SpatialCoordinates d → ℝ) (Cpsi : ℝ),
      ContDiff ℝ 2 psi → c2Norm (closedCube (triadicGridCenter z r q)
        (triadicGridSide r q) (triadicGridSide_pos hr q)) psi ≤ Cpsi →
      ∀ b' u' : weakSobolevGraph
          (centeredCube (triadicGridCenter z r q) (triadicGridSide r q)
            (triadicGridSide_pos hr q)),
        ((b'.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (triadicGridCenter z r q) (triadicGridSide r q)
            (triadicGridSide_pos hr q) : Set (SpatialCoordinates d))] psi) →
        SolvesDirichlet
          (cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n))
            (triadicGridCenter z r q) (triadicGridSide_pos hr q))
          (fun _ => 0) b' u' →
        ∃ V : SpatialCoordinates d → ℝ, Continuous V ∧
          ((u'.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube (triadicGridCenter z r q) (triadicGridSide r q)
              (triadicGridSide_pos hr q) : Set (SpatialCoordinates d))] V) ∧
          IsHolderOn alpha (closure (centeredCube (triadicGridCenter z r q)
            (triadicGridSide r q) (triadicGridSide_pos hr q) : Set (SpatialCoordinates d))) V ∧
          cAlphaNorm alpha (closure (centeredCube (triadicGridCenter z r q)
            (triadicGridSide r q) (triadicGridSide_pos hr q) : Set (SpatialCoordinates d))) V ≤
            Kgrowth * Cpsi := by
    intro n psi Cpsi hpsi hCpsi b' u' hb' hu'
    have hpsi2 : ContDiff ℝ 2 psi := hpsi
    obtain ⟨V, hVcont, hVae, hVholder, hVnorm⟩ :=
      hgrowthOm q (seq n) psi Cpsi hpsi2 hCpsi b' u' hb' hu'
    have hCpsi0 : 0 ≤ Cpsi :=
      (aux_prop_growth_c2Norm_nonneg _ _).trans hCpsi
    have hbankBound : growthBank q (seq n) om ≤ Kgrowth :=
      (le_abs_self _).trans (hGrowthCap n)
    refine ⟨V, hVcont, hVae, hVholder, ?_⟩
    exact hVnorm.trans (mul_le_mul_of_nonneg_right hbankBound hCpsi0)
  exact smooth_minimizer_regularity_of_growth
    (triadicGridCenter z r q) (triadicGridSide r q) (triadicGridSide_pos hr q)
    (centeredCube_killedPoincare (triadicGridCenter z r q) (triadicGridSide_pos hr q))
    (fun n => cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n))
      (triadicGridCenter z r q) (triadicGridSide_pos hr q))
    alpha Kgrowth hKgrowth hGrowthUniform phi hphi b hb
end Paper
