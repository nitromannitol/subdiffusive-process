module

public import SubdiffusiveProcess.Paper.mfd_prop_boundary
public import SubdiffusiveProcess.Section9.SmoothCellMesh

@[expose] public section




set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Construct a smooth catalogue patch and all its boundary conclusions from the
actual represented data; this supplies the smooth approximants for Hölder completion. -/
theorem aux_mfd_prop_gluing_smooth_trace_package
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ) (hr : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (rad j) (hr j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hr j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hr j) : Set (SpatialCoordinates d)))
    (Cext : ℝ) (beta alpha eta t : ℝ) (orders : Finset ℝ)
    (E : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (omega : Ω) (iQ : J)
    (zq : SpatialCoordinates d) (rq : ℝ) (hrq : 0 < rq) (h3rq : 0 < 3 * rq)
    (hz : z iQ = zq) (hrad : rad iQ = 3 * rq)
    (S0 : ResponseSpace (centeredCube zq (3 * rq) h3rq))
    (G0 : DomainL2 (centeredCube zq (3 * rq) h3rq) →L[ℝ]
      DomainL2 (centeredCube zq (3 * rq) h3rq))
    (L : aux_limit_form_package_limit_side d hd zq (3 * rq) h3rq S0 G0
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n) zq h3rq))
    (g : D iQ)
    (hR : conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hr S D f T theta thetaH1
      usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey) (hmem : omega ∈ G)
    (hS0 : S0.space = killedSobolevGraph (centeredCube zq (3 * rq) h3rq)) :
    ∃ (PhiH : H1Function (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)))
      (Phiq : H1Function (centeredCube zq rq hrq : Set (SpatialCoordinates d)))
      (W : ℕ → H1Function (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)))
      (WS : ℕ → S0.space)
      (U : DomainL2 (centeredCube zq (3 * rq) h3rq)) (Uc : SpatialCoordinates d → ℝ),
      PhiH.toFun = f iQ g ∧ Phiq.toFun = f iQ g ∧
      (∀ n, (WS n).val = sobolevDataOfH1 (W n) ∧
        ContinuousOn (W n).toFun (closure (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))) ∧
        (∀ x ∈ frontier (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)), (W n).toFun x = 0) ∧
        ∀ c : OddGridIndex d (triadicHalf 1),
          IsWeaklyHarmonicOn (cutoffCoefficient M H (env n omega) (cutoff n))
            (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) c : Set (SpatialCoordinates d))
            ((W n).restrict (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) c).isOpen
              (oddGridCell_subset zq h3rq (triadicHalf 1) c)) ∧
          HasZeroTraceDifferenceOn
            (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) c : Set (SpatialCoordinates d))
            ((W n).restrict (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) c).isOpen
              (oddGridCell_subset zq h3rq (triadicHalf 1) c))
            (PhiH.restrict (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) c).isOpen
              (oddGridCell_subset zq h3rq (triadicHalf 1) c)) ∧
          (∀ x ∈ frontier (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) c : Set (SpatialCoordinates d)),
            (W n).toFun x = f iQ g x)) ∧
    U ∈ L.form.domain ∧
    ContinuousOn Uc (closure (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))) ∧
    (U : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))] Uc ∧
    TendstoUniformlyOn (fun n => (W n).toFun) Uc atTop
      (closure (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))) ∧
    (∀ x ∈ frontier (centeredCube zq rq hrq : Set (SpatialCoordinates d)), Uc x = f iQ g x) ∧
    L.gamma.measure U (frontier (centeredCube zq rq hrq : Set (SpatialCoordinates d))) = 0 ∧
    (∀ phi : DomainL2 (centeredCube zq (3 * rq) h3rq),
      phi ∈ L.form.toClosedForm.killedCoreClosure
        (centeredCube zq rq hrq : Set (SpatialCoordinates d)) → L.form.form U phi = 0) ∧
    Tendsto (fun n => cellDirichletInfimum
      (cutoffCoefficient M H (env n omega) (cutoff n))
      (centeredCube zq rq hrq : Set (SpatialCoordinates d)) Phiq) atTop
      (𝓝 ((L.gamma.measure U (centeredCube zq rq hrq : Set (SpatialCoordinates d))).toReal)) ∧
    (∀ V ∈ L.form.domain, ∀ Vc : SpatialCoordinates d → ℝ,
      ContinuousOn Vc (closure (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))) →
      (V : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))] Vc →
      (∀ x ∈ frontier (centeredCube zq rq hrq : Set (SpatialCoordinates d)), Vc x = f iQ g x) →
      (L.gamma.measure U (centeredCube zq rq hrq : Set (SpatialCoordinates d))).toReal ≤
        (L.gamma.measure V (centeredCube zq rq hrq : Set (SpatialCoordinates d))).toReal)
 := by
  classical
  have hSource := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 iQ g
  have hQeq : centeredCube (z iQ) (rad iQ) (hr iQ) = centeredCube zq (3 * rq) h3rq := by
    apply SetLike.coe_injective
    change Metric.ball (z iQ) (rad iQ / 2) = Metric.ball zq (3 * rq / 2)
    rw [hz, hrad]
  have hSupp : tsupport (f iQ g) ⊆ (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)) := by
    simpa only [hQeq] using hSource.2.2.1
  obtain ⟨PhiH, W, WS, hPhiH, hW⟩ := SubdiffusiveProcess.Section9.exists_smooth_cell_mesh hd zq (3 * rq)
    h3rq S0 hS0 (fun n => cutoffCoefficient M H (env n omega) (cutoff n))
    (fun n => aux_mfd_prop_boundary_cutoff_continuous M H (env n omega) (cutoff n))
    (fun n => aux_mfd_prop_boundary_cutoff_elliptic_closure M H (env n omega) (cutoff n) _ _ _)
    (f iQ g) hSource.1 hSource.2.1 hSupp
  obtain ⟨U, Uc, h1, h2, h3, h4, h5, h6, h7, hbq, h9⟩ := mfd_prop_boundary
    d hd M H Ω P cutoff env J j0 z rad hr S D f T theta thetaH1 usrc srcRep ucell
    Cext beta alpha eta t orders E Index resp respLim constants G coercivityKey extensionKey
    lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey Grid origin gridRoot gridKey omega iQ zq rq hrq h3rq hz hrad S0 G0 L
    g PhiH W WS hR hmem hS0 hPhiH (fun n => (hW n).1) (fun k n => (hW n).2.2.2 k)
  obtain ⟨Phiq, hPhiq, h8⟩ := hbq
  refine ⟨PhiH, Phiq, W, WS, U, Uc, hPhiH, hPhiq, ?_, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  intro n
  refine ⟨(hW n).1, (hW n).2.1, (hW n).2.2.1, ?_⟩
  intro c
  exact ⟨((hW n).2.2.2 c).1, ((hW n).2.2.2 c).2.1, ((hW n).2.2.2 c).2.2.2⟩

end SubdiffusiveProcess.Paper
