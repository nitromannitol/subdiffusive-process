module

public import SubdiffusiveProcess.Paper.affine_source_cells_mass
public import SubdiffusiveProcess.Paper.represented_limit_planes_null

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped Topology ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The represented catalogue supplies both mass-cell indices and coordinate-plane nullity.
Thus its affine conclusion applies on half-open cells for every regular form with the inverse limit,
without either geometric-coverage or plane-nullity supplier premises. -/
theorem affine_source_cells_mass_represented
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (j0 : ℕ)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (r j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (r j) (hr j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : ℕ → Type) [hTc : ∀ j, Countable (T j)]
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
    (E : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : ℕ → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → ℕ) (gridKey : Grid → Index)
    (hRep : conv_represented_estimates d hd M H Ω P cutoff env ℕ j0 z r hr S D f T theta thetaH1
      usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (field : Ω → BilateralField d) (jQ : ℕ)
    (GN : ℕ → Ω → DomainL2 (centeredCube (z jQ) (r jQ) (hr jQ)) →L[ℝ]
      DomainL2 (centeredCube (z jQ) (r jQ) (hr jQ)))
    (GEj : Ω → DomainL2 (centeredCube (z jQ) (r jQ) (hr jQ)) →L[ℝ]
      DomainL2 (centeredCube (z jQ) (r jQ) (hr jQ)))
    (hGN : ∀ᵐ omega ∂P, ∀ n f, GN n omega f =
      (responseSolution (S jQ)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z jQ) (hr jQ))
        ((sobolevVolumeLoad f).comp (S jQ).space.subtypeL)).val.1)
    (hConv : ∀ᵐ omega ∂P, Tendsto (fun n => GN n omega) atTop (𝓝 (GEj omega)))
    (hBounds : ∀ᵐ omega ∂P, in_represented_bounds_seq d hd (z jQ) (r jQ) (hr jQ) (S jQ)
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z jQ) (hr jQ))
      (GEj omega))
    (g : aux_thm_prop_selection_geometry d) (Good : ℕ → SpatialCoordinates d → Set Ω)
    (k0 : ℕ) (lambdaLim cell epshom cdet : ℝ) (hwidth : 81 ≤ g.width)
    (MassGrid : Type) (massOrigin : MassGrid → SpatialCoordinates d)
    (massGridChoice : Fin (Fintype.card (Fin d → Fin g.Mm)) → MassGrid)
    (hgc : ∀ sigma : Fin d → Fin g.Mm,
      massOrigin (massGridChoice (Fintype.equivFin (Fin d → Fin g.Mm) sigma)) =
        fun i => ((sigma i).val : ℝ) / (g.Mm : ℝ) + 1 / 2)
    (ZLim DLim : (ℕ × ℕ) → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
    (loLim hiLim : (ℕ × ℕ) → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
    (errLim ratioLim : (ℕ × ℕ) → Unit → BilateralField d → ℝ)
    (hConcl : aux_affine_source_cells_env_Concl (z jQ) (r jQ) (hr jQ) P field GEj g.gamma
      g.zeta (3 / 2048) g.H1 k0 lambdaLim cell epshom cdet MassGrid massOrigin
      (Fintype.card (Fin d → Fin g.Mm)) massGridChoice
      (fun c : ℕ × ℕ => g.H1 * c.2) (fun c => z c.1) ZLim DLim loLim hiLim errLim
      ratioLim)
    (hGood : ∀ n zc, aux_thm_prop_cell_available z r zc (aux_thm_prop_mass_side g.H1 n) →
      ∀ om ∈ Good n zc, field om ∈ gcat_good k0 lambdaLim cell epshom cdet
        (ZLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (DLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (loLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (hiLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (errLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (ratioLim ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))) :
    ∀ᵐ omega ∂P,
      ∀ (E' : _root_.SubdiffusiveProcess.DirichletForm
          (volume.restrict (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))))
        (Gam' : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E'.toClosedForm),
      (∀ u, E'.toClosedForm.energy u = limitFormEnergy (GEj omega) u) →
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E'.toClosedForm
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) C) →
      ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z jQ) (r jQ) (hr jQ)),
      ∀ _hu : GEj omega f ∈ E'.toClosedForm.domain, ∀ c : ℝ, 0 < c →
      ∃ baseMesh : ℝ, 0 < baseMesh ∧
        ∀ (n : ℕ), 1 ≤ n → aux_thm_prop_mass_side g.H1 n ≤ baseMesh →
        ∀ (sigma : Fin d → Fin g.Mm) (k : Fin d → ℤ),
        omega ∈ Good n (aux_thm_prop_mass_center g.H1 g.Mm sigma n k) →
        aux_thm_prop_mass_padded g.H1 g.Mm g.width g.gamma sigma n k →
        closure (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k) ⊆
          (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
        let mu := Gam'.measure (GEj omega f) + ENNReal.ofReal c •
          volume.restrict (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))
        (mu (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k)).toReal ≤
          ((3 : ℝ) ^ g.H1) ^ ((d : ℝ) + g.zeta) *
            (mu (aux_thm_prop_mass_cell g.H1 g.Mm sigma n k)).toReal →
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))) ∧
          (⇑(GEj omega f) =ᵐ[volume.restrict
            (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))] U) ∧
          aux_thm_prop_affine_error (centeredCube (z jQ) (r jQ) (hr jQ))
            E'.toClosedForm Gam' (GEj omega f) U c
            (centeredCube (aux_thm_prop_mass_center g.H1 g.Mm sigma n k)
              (aux_thm_prop_mass_side g.H1 n) (aux_thm_prop_grid_side_pos g.H1 n) :
                Set (SpatialCoordinates d)) := by
  have hMass := hRep
  rcases hMass with ⟨_, _, _, _, _, _, _, _, _, _, hcontain, _, _, hcomplete, _⟩
  have hmass := aux_thm_prop_mass_catalogue_indices j0 z r hr hcontain hcomplete jQ
  have h := affine_source_cells_mass hd P field z r hr jQ GEj g Good k0 lambdaLim cell epshom
    cdet hwidth MassGrid massOrigin massGridChoice hgc ZLim DLim loLim hiLim errLim ratioLim
    hConcl hmass hGood
  have hevent : ∀ᵐ omega ∂P, omega ∈ G :=
    ae_iff.mpr hRep.2.2.2.2.2.2.2.2.2.1.2.2.1
  filter_upwards [h, hevent, hGN, hConv, hBounds] with omega hω hom hN hL hB
  intro Ef Gamma hEf hcore
  have hplanes := represented_limit_planes_null d hd M H Ω P cutoff env ℕ j0 z r hr S D f T
    theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hRep omega hom jQ
    (fun n => GN n omega) (GEj omega) hB hN hL Ef hEf hcore Gamma
  exact hω Ef Gamma hEf hcore hplanes

end SubdiffusiveProcess.Paper
