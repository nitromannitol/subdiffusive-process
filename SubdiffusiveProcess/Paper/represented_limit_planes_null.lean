module

public import SubdiffusiveProcess.Paper.thm_prop_base
public import SubdiffusiveProcess.Paper.conv_represented_limit_forms
public import SubdiffusiveProcess.Paper.limit_form_package_controls

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- The actual varying-environment catalogue and represented bounds imply zero mass
on coordinate planes for every energy measure of a regular form with the given inverse limit.
No plane-nullity or additional analytic control hypothesis is required. -/
theorem represented_limit_planes_null
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (r j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (r j) (hr j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (Cext : ℝ) (beta alpha eta t : ℝ) (orders : Finset ℝ)
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (hRep : conv_represented_estimates d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1
      usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (om : Ω) (hom : om ∈ G) (j : J)
    (GN : ℕ → DomainL2 (centeredCube (z j) (r j) (hr j)) →L[ℝ]
      DomainL2 (centeredCube (z j) (r j) (hr j)))
    (Glim : DomainL2 (centeredCube (z j) (r j) (hr j)) →L[ℝ]
      DomainL2 (centeredCube (z j) (r j) (hr j)))
    (hBounds : in_represented_bounds_seq d hd (z j) (r j) (hr j) (S j)
      (fun n => Lane4.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j)) Glim)
    (hGN : ∀ n f, GN n f =
      (responseSolution (S j)
        (Lane4.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j))
        ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 Glim))
    (EForm : _root_.DirichletForm
      (volume.restrict (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))))
    (hE : ∀ u, EForm.energy u = limitFormEnergy Glim u)
    (hcore : ∃ C, DirichletForm.IsCoreOn EForm.toClosedForm
      (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) C)
    (Gamma : DirichletForm.EnergyMeasure EForm.toClosedForm) :
    ∀ u ∈ EForm.domain, ∀ (i : Fin d) (c : ℝ),
      Gamma.measure u {x : SpatialCoordinates d | x i = c} = 0 := by
  obtain ⟨A⟩ := aux_limit_form_package_controls_of_bounds hd (z j) (r j) (hr j) (S j)
    Glim _ hBounds
  let B : aux_thm_prop_analytic_controls d hd (z j) (r j) (hr j) (S j)
      (fun n => Lane4.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j)) := {
    K := A.K, K_pos := A.K_pos, coercive := A.coercive
    interpolation := A.interpolation, sources := A.sources
    sources_countable := A.sources_countable, sources_dense := A.sources_dense
    sources_smooth := A.sources_smooth, mesh := A.mesh
    t := A.t, t_lower := A.t_lower, t_upper := A.t_upper, cutoffs := A.cutoffs }
  exact aux_thm_prop_represented_domain_planes_null d hd
    (inputs_BD_witness d) (inputs_BDQ_witness d) (inputs_EM_witness d)
    (inputs_classical_e6_response_hcontract d) M H Ω P cutoff env J j0 z r hr S D f T
    theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hRep om hom j B
    GN Glim hGN hConv EForm hE hcore Gamma

end Paper
