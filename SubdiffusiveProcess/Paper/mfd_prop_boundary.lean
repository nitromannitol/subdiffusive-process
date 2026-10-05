module

public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.limit_form_package_side
public import SubdiffusiveProcess.DirichletForm.KilledCoreClosure
public import SubdiffusiveProcess.Paper.prop_boundary
public import SubdiffusiveProcess.Paper.Support.B7cBoundaryCompletion
public import SubdiffusiveProcess.Paper.Support.B7cCutoffExponent
public import SubdiffusiveProcess.Paper.Support.B7cCatalogueBounds
public import SubdiffusiveProcess.Paper.limit_form_killed_consistency
@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Exact proposed closed proposition for the repaired boundary principal.
The only estimate predicate is the existing ACTUAL represented catalogue,
whose fields and actual-model producer are unchanged. No solution-limit,
energy-measure convergence, truncation or finite-cell estimates are premises. -/
def aux_mfd_prop_boundary_statement
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
    (_hz : z iQ = zq) (_hrad : rad iQ = 3 * rq)
    (S0 : ResponseSpace (centeredCube zq (3 * rq) h3rq))
    (G0 : DomainL2 (centeredCube zq (3 * rq) h3rq) →L[ℝ]
      DomainL2 (centeredCube zq (3 * rq) h3rq))
    (L : aux_limit_form_package_limit_side d hd zq (3 * rq) h3rq S0 G0
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n) zq h3rq))
    (g : D iQ)
    (betaQ : H1Function (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)))
    (UN : ℕ → H1Function (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)))
    (UNS : ℕ → S0.space) : Prop :=
  conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hr
      S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
      Index resp respLim constants G coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
      cellGrowthKey cellHolderKey Grid origin gridRoot gridKey → omega ∈ G →
  S0.space = killedSobolevGraph (centeredCube zq (3 * rq) h3rq) →
  betaQ.toFun = f iQ g →
  (∀ n, (UNS n : SobolevData (centeredCube zq (3 * rq) h3rq)) = sobolevDataOfH1 (UN n)) →
  (∀ k : OddGridIndex d (triadicHalf 1),
    let qk := oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k
    let hsub := oddGridCell_subset zq h3rq (triadicHalf 1) k
    ∀ n,
      IsWeaklyHarmonicOn (cutoffCoefficient M H (env n omega) (cutoff n))
        (qk : Set (SpatialCoordinates d)) ((UN n).restrict qk.isOpen hsub) ∧
      HasZeroTraceDifferenceOn (qk : Set (SpatialCoordinates d))
        ((UN n).restrict qk.isOpen hsub) (betaQ.restrict qk.isOpen hsub) ∧
      ContinuousOn (UN n).toFun (closure (qk : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (qk : Set (SpatialCoordinates d)), (UN n).toFun x = f iQ g x)) →
  ∃ (U : DomainL2 (centeredCube zq (3 * rq) h3rq)) (Uc : SpatialCoordinates d → ℝ),
    U ∈ L.form.domain ∧
    ContinuousOn Uc (closure (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))) ∧
    (U : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))] Uc ∧
    TendstoUniformlyOn (fun n => (UN n).toFun) Uc atTop
      (closure (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))) ∧
    (∀ x ∈ frontier (centeredCube zq rq hrq : Set (SpatialCoordinates d)), Uc x = f iQ g x) ∧
    L.gamma.measure U (frontier (centeredCube zq rq hrq : Set (SpatialCoordinates d))) = 0 ∧
    (∀ phi : DomainL2 (centeredCube zq (3 * rq) h3rq),
      phi ∈ L.form.toClosedForm.killedCoreClosure
        (centeredCube zq rq hrq : Set (SpatialCoordinates d)) → L.form.form U phi = 0) ∧
    (∃ betaq : H1Function (centeredCube zq rq hrq : Set (SpatialCoordinates d)),
      betaq.toFun = f iQ g ∧
      Tendsto (fun n => cellDirichletInfimum
        (cutoffCoefficient M H (env n omega) (cutoff n))
        (centeredCube zq rq hrq : Set (SpatialCoordinates d)) betaq) atTop
        (𝓝 ((L.gamma.measure U (centeredCube zq rq hrq : Set (SpatialCoordinates d))).toReal))) ∧
    (∀ V ∈ L.form.domain, ∀ Vc : SpatialCoordinates d → ℝ,
      ContinuousOn Vc (closure (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))) →
      (V : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))] Vc →
      (∀ x ∈ frontier (centeredCube zq rq hrq : Set (SpatialCoordinates d)), Vc x = f iQ g x) →
      (L.gamma.measure U (centeredCube zq rq hrq : Set (SpatialCoordinates d))).toReal ≤
        (L.gamma.measure V (centeredCube zq rq hrq : Set (SpatialCoordinates d))).toReal)


/-- Faithful boundary proposition for catalogue traces. The ACTUAL standing record and
limit-side package are produced by conv_represented_thm_c1_hyp_grids_actual_root,
conv_represented_joint_grids_buffered, conv_represented_joint_bounds and
conv_represented_limit_forms (B1 actual-model capstone). Their bounds include only
proved outputs of that chain. beta is the common source-catalogue datum used by gluing;
finite interpolants are supplied by their defining PDE, trace and representation data.
No solution limit, recovery, growth, truncation or uniqueness is assumed. -/
theorem mfd_prop_boundary : ∀
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
    [_hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [_hTc : ∀ j, Countable (T j)]
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
    (betaQ : H1Function (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)))
    (UN : ℕ → H1Function (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)))
    (UNS : ℕ → S0.space),
    aux_mfd_prop_boundary_statement d hd M H Ω P cutoff env J j0 z rad hr S D f T theta thetaH1 usrc srcRep ucell
      Cext beta alpha eta t orders E Index resp respLim constants G coercivityKey
      extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey
      omega iQ zq rq hrq h3rq hz hrad S0 G0 L g betaQ UN UNS := by
  intro d hd _ _ M H Ω _ P _ cutoff env J _ _ j0 z rad hr S D _ f T _ theta thetaH1
    usrc srcRep ucell Cext beta alpha eta t orders E Index _ resp respLim constants G
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid _ origin gridRoot gridKey
    omega iQ zq rq hrq h3rq hz hrad S0 G0 L g betaQ UN UNS
  unfold aux_mfd_prop_boundary_statement
  intro hR hmem hS0 hBeta hUNrep hFinite
  classical
  let Q := centeredCube zq (3 * rq) h3rq
  let q := centeredCube zq rq hrq
  let a : ℕ → SpatialCoordinates d → ℝ :=
    fun n => cutoffCoefficient M H (env n omega) (cutoff n)
  let aC : ℕ → PositiveCoefficient Q :=
    fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n) zq h3rq
  have hCont : ∀ n, ContinuousOn (a n) (closure (Q : Set (SpatialCoordinates d))) :=
    fun n => (aux_mfd_prop_boundary_cutoff_continuous M H (env n omega) (cutoff n)).continuousOn
  have hAe : ∀ n, ((aC n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] a n :=
    fun n => FiniteStopping.cutoffCoefficient_ae M H (env n omega) (cutoff n) zq h3rq
  have hEll : ∀ n, ∃ lo hi : ℝ, 0 < lo ∧
      ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), lo ≤ a n x ∧ a n x ≤ hi :=
    fun n => aux_mfd_prop_boundary_cutoff_elliptic_closure M H (env n omega) (cutoff n)
      zq (3 * rq) h3rq
  obtain ⟨Bcell, Hcell, hBH, hNative⟩ := aux_mfd_prop_boundary_catalogue_bounds
    d hd M H Ω P cutoff env J j0 z rad hr S D f T theta thetaH1 usrc srcRep ucell
    Cext beta alpha eta t orders E Index resp respLim constants G coercivityKey extensionKey
    lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey Grid origin gridRoot gridKey hR omega hmem iQ zq rq hrq h3rq hz hrad
    g betaQ hBeta UN (fun k n => ⟨(hFinite k n).1, (hFinite k n).2.1, (hFinite k n).2.2.1⟩)
  have hSource := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 iQ g
  have hSupport : tsupport (f iQ g) ⊆ (Q : Set (SpatialCoordinates d)) := by
    have hQeq : centeredCube (z iQ) (rad iQ) (hr iQ) = Q := by
      apply SetLike.coe_injective
      change Metric.ball (z iQ) (rad iQ / 2) = Metric.ball zq (3 * rq / 2)
      rw [hz, hrad]
    simpa only [hQeq] using hSource.2.2.1
  exact aux_mfd_prop_boundary_from_native_bounds d hd zq rq hrq h3rq S0 hS0 a aC
    hCont hAe hEll (f iQ g) ⟨hSource.1, hSource.2.1, hSupport⟩ betaQ hBeta UN UNS hUNrep
    hFinite t alpha hR.1.1 hR.1.2 (hR.2.2.1.1.trans hR.2.2.1.2) hR.2.1.1
    Bcell Hcell hBH hNative G0 L


end SubdiffusiveProcess.Paper
