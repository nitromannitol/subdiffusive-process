module

public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.limit_form_package_side
public import SubdiffusiveProcess.DirichletForm.KilledCoreClosure
public import SubdiffusiveProcess.Paper.prop_gluing

@[expose] public section




set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace Paper

/-- The geometric triple-enlargement interface used by the exact statement. -/
theorem aux_mfd_prop_gluing_triple_subset
    {d : ℕ} (zq zQ : SpatialCoordinates d) (rq RQ : ℝ)
    (hrq : 0 < rq) (hRQ : 0 < RQ) (hz : zQ = zq) (hrad : RQ = 3 * rq) :
    (centeredCube zq rq hrq : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d)) := by
  change Metric.ball zq (rq / 2) ⊆ Metric.ball zQ (RQ / 2)
  rw [hz, hrad]
  exact Metric.ball_subset_ball (by linarith only [hrq])

/-- Actual trace completion package: every finite object and every limiting property
is a conclusion. The continuous version and L2 version of U live on the triple cube. -/
def aux_mfd_prop_gluing_trace_package
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (w : ℕ → BilateralField d) (cutoff : ℕ → ℕ)
    (zq : SpatialCoordinates d) (rq : ℝ) (hrq : 0 < rq)
    (zQ : SpatialCoordinates d) (RQ : ℝ) (hRQ : 0 < RQ)
    (hz : zQ = zq) (hrad : RQ = 3 * rq)
    (S0 : ResponseSpace (centeredCube zQ RQ hRQ))
    (G0 : DomainL2 (centeredCube zQ RQ hRQ) →L[ℝ]
      DomainL2 (centeredCube zQ RQ hRQ))
    (L0 : aux_limit_form_package_limit_side d hd zQ RQ hRQ S0 G0
      (fun n => Lane4.cutoffPositiveCoefficient M H (w n) (cutoff n) zQ hRQ))
    (Ein : Paper.in_J d) (Cext beta alpha : ℝ)
    (b : SpatialCoordinates d → ℝ)
    (lam : ℝ) (U : DomainL2 (centeredCube zQ RQ hRQ))
    (Uc : SpatialCoordinates d → ℝ) : Prop :=
  ∃ (B : SpatialCoordinates d → ℝ)
    (UN : ℕ → H1Function (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d)))
    (UNS : ℕ → S0.space),
    IsCellBoundaryClass beta zq rq b ∧
    Continuous B ∧ HasCompactSupport B ∧
    tsupport B ⊆ (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d)) ∧
    Lane4.IsHolderOn alpha Set.univ B ∧
    EqOn B b (frontier (centeredCube zq rq hrq : Set (SpatialCoordinates d))) ∧
    (∀ n, (UNS n).val = sobolevDataOfH1 (UN n) ∧
      ContinuousOn (UN n).toFun
        (closure (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d)),
        (UN n).toFun x = 0) ∧
      ∀ k : OddGridIndex d (triadicHalf 1),
        IsWeaklyHarmonicOn (cutoffCoefficient M H (w n) (cutoff n))
          (oddGridCell zQ RQ hRQ (triadicHalf 1) k : Set (SpatialCoordinates d))
          ((UN n).restrict (oddGridCell zQ RQ hRQ (triadicHalf 1) k).isOpen
            (oddGridCell_subset zQ hRQ (triadicHalf 1) k)) ∧
        (∀ x ∈ frontier (oddGridCell zQ RQ hRQ (triadicHalf 1) k :
            Set (SpatialCoordinates d)), (UN n).toFun x = B x)) ∧
    Tendsto (fun n => cellDirichletInfimum (cutoffCoefficient M H (w n) (cutoff n))
      (centeredCube zq rq hrq : Set (SpatialCoordinates d))
      ((UN n).restrict (centeredCube zq rq hrq).isOpen
        (aux_mfd_prop_gluing_triple_subset zq zQ rq RQ hrq hRQ hz hrad))) atTop (𝓝 lam) ∧
    BddAbove (Set.range (fun n => Ein.Lam zq rq hrq
      (Lane4.cutoffPositiveCoefficient M H (w n) (cutoff n) zq hrq)
      zq rq ((beta - 1 / 2) / 4) 2)) ∧
    lam ≤ Cext * sSup (Set.range (fun n => Ein.Lam zq rq hrq
      (Lane4.cutoffPositiveCoefficient M H (w n) (cutoff n) zq hrq)
      zq rq ((beta - 1 / 2) / 4) 2)) * rq ^ ((d : ℝ) - 2) *
        cellBoundaryQuotientNorm beta zq rq b ^ 2 ∧
    U ∈ L0.form.domain ∧
    ContinuousOn Uc (closure (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))) ∧
    (U : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))] Uc ∧
    TendstoUniformlyOn (fun n => (UN n).toFun) Uc atTop
      (closure (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))) ∧
    EqOn Uc b (frontier (centeredCube zq rq hrq : Set (SpatialCoordinates d))) ∧
    L0.gamma.measure U (frontier (centeredCube zq rq hrq : Set (SpatialCoordinates d))) = 0 ∧
    (∀ phi ∈ L0.form.toClosedForm.killedCoreClosure
        (centeredCube zq rq hrq : Set (SpatialCoordinates d)), L0.form.form U phi = 0) ∧
    (L0.gamma.measure U (centeredCube zq rq hrq : Set (SpatialCoordinates d))).toReal = lam ∧
    (∀ V ∈ L0.form.domain, ∀ Vc : SpatialCoordinates d → ℝ,
      ContinuousOn Vc (closure (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))) →
      (V : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))] Vc →
      EqOn Vc b (frontier (centeredCube zq rq hrq : Set (SpatialCoordinates d))) →
      (L0.gamma.measure U (centeredCube zq rq hrq : Set (SpatialCoordinates d))).toReal ≤
        (L0.gamma.measure V (centeredCube zq rq hrq : Set (SpatialCoordinates d))).toReal)

/-- All three paper clauses assembled. R is the existing represented standing convention;
Ls is the family supplied by the actual represented limit-form producer, not Ui properties. -/
def aux_mfd_prop_gluing_statement
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
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
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (omega : Ω)
    (Gs : ∀ j, DomainL2 (centeredCube (z j) (rad j) (hr j)) →L[ℝ]
      DomainL2 (centeredCube (z j) (rad j) (hr j)))
    (Ls : ∀ j, aux_limit_form_package_limit_side d hd (z j) (rad j) (hr j) (S j) (Gs j)
      (fun n => Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j) (hr j))) : Prop :=
  conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hr
    S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
    Index resp respLim constants G coercivityKey extensionKey lambdaKey
    sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
    cellGrowthKey cellHolderKey Grid origin gridRoot gridKey → omega ∈ G →
  -- (i) Every trace on every catalogue cube has its extension and its actual energy limit.
  (∀ (iq iQ : J) (hz : z iQ = z iq) (hrad : rad iQ = 3 * rad iq),
    ∀ b : SpatialCoordinates d → ℝ,
      Lane4.IsHolderOn alpha
        (frontier (centeredCube (z iq) (rad iq) (hr iq) : Set (SpatialCoordinates d))) b →
      ∃ lam : ℝ, ∃ U : DomainL2 (centeredCube (z iQ) (rad iQ) (hr iQ)),
        ∃ Uc : SpatialCoordinates d → ℝ,
          aux_mfd_prop_gluing_trace_package d hd M H (fun n => env n omega) cutoff
            (z iq) (rad iq) (hr iq) (z iQ) (rad iQ) (hr iQ) hz hrad (S iQ)
            (Gs iQ) (Ls iQ) E Cext beta alpha b lam U Uc) ∧
  -- (ii), with (iii) as the additional conclusion under its paper hypothesis.
  (∀ (iQ : J) (m : ℕ) (iq iQcell : Fin m → J)
    (hz : ∀ i, z (iQcell i) = z (iq i))
    (hrad : ∀ i, rad (iQcell i) = 3 * rad (iq i))
    (hCell : ∀ i, closure (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) :
        Set (SpatialCoordinates d)) ⊆
      (centeredCube (z iQ) (rad iQ) (hr iQ) : Set (SpatialCoordinates d)))
    (hEnlarge : ∀ i, (centeredCube (z (iQcell i)) (rad (iQcell i)) (hr (iQcell i)) :
        Set (SpatialCoordinates d)) ⊆
      (centeredCube (z iQ) (rad iQ) (hr iQ) : Set (SpatialCoordinates d)))
    (hDisjoint : Pairwise fun i j : Fin m => Disjoint
      (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) : Set (SpatialCoordinates d))
      (centeredCube (z (iq j)) (rad (iq j)) (hr (iq j)) : Set (SpatialCoordinates d)))
    (V : DomainL2 (centeredCube (z iQ) (rad iQ) (hr iQ)))
    (hV : V ∈ (Ls iQ).form.domain) (Vc : SpatialCoordinates d → ℝ)
    (hVc : ContinuousOn Vc (closure (centeredCube (z iQ) (rad iQ) (hr iQ) : Set (SpatialCoordinates d))))
    (hVrep : (V : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube (z iQ) (rad iQ) (hr iQ) : Set (SpatialCoordinates d))] Vc)
    (hTrace : ∀ i, Lane4.IsHolderOn alpha
      (frontier (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) : Set (SpatialCoordinates d))) Vc),
    ∃ (Lam : Fin m → ℝ)
      (Ui : Fin m → SpatialCoordinates d → ℝ)
      (UiL2 : Fin m → DomainL2 (centeredCube (z iQ) (rad iQ) (hr iQ)))
      (Vprime : DomainL2 (centeredCube (z iQ) (rad iQ) (hr iQ))),
      let Vprimec := fun x => Vc x + ∑ i : Fin m,
        (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) : Set (SpatialCoordinates d)).indicator
          (fun y => Ui i y - Vc y) x
      (∀ i,
        ∃ U : DomainL2 (centeredCube (z (iQcell i)) (rad (iQcell i)) (hr (iQcell i))),
          aux_mfd_prop_gluing_trace_package d hd M H (fun n => env n omega) cutoff
            (z (iq i)) (rad (iq i)) (hr (iq i))
            (z (iQcell i)) (rad (iQcell i)) (hr (iQcell i))
            (hz i) (hrad i)
            (S (iQcell i)) (Gs (iQcell i)) (Ls (iQcell i))
            E Cext beta alpha Vc (Lam i) U (Ui i)) ∧
      (∀ i, UiL2 i ∈ (Ls iQ).form.domain ∧
        (UiL2 i : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube (z iQ) (rad iQ) (hr iQ) : Set (SpatialCoordinates d))]
          ((centeredCube (z (iQcell i)) (rad (iQcell i)) (hr (iQcell i)) : Set (SpatialCoordinates d)).indicator (Ui i))) ∧
      Vprime ∈ (Ls iQ).form.domain ∧
      ContinuousOn Vprimec (closure (centeredCube (z iQ) (rad iQ) (hr iQ) : Set (SpatialCoordinates d))) ∧
      (Vprime : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube (z iQ) (rad iQ) (hr iQ) : Set (SpatialCoordinates d))] Vprimec ∧
      (Ls iQ).form.form Vprime Vprime = (Ls iQ).form.form V V - ∑ i : Fin m,
        (((Ls iQ).gamma.measure V
          (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) : Set (SpatialCoordinates d))).toReal - Lam i) ∧
      (Ls iQ).form.form Vprime Vprime ≤ (Ls iQ).form.form V V ∧
      (∀ i, ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        B ⊆ (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) : Set (SpatialCoordinates d)) →
        (Ls iQ).gamma.measure Vprime B = (Ls iQ).gamma.measure (UiL2 i) B) ∧
      (∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        B ⊆ (centeredCube (z iQ) (rad iQ) (hr iQ) : Set (SpatialCoordinates d)) \
          (⋃ i : Fin m, (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) : Set (SpatialCoordinates d))) →
        (Ls iQ).gamma.measure Vprime B = (Ls iQ).gamma.measure V B) ∧
      (∀ (zprime : SpatialCoordinates d) (rprime : ℝ) (hrprime : 0 < rprime),
        closure (centeredCube zprime rprime hrprime : Set (SpatialCoordinates d)) =
          ⋃ i : Fin m, closure (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) : Set (SpatialCoordinates d)) →
        (∀ i, (Ls iQ).gamma.measure V
          (frontier (centeredCube (z (iq i)) (rad (iq i)) (hr (iq i)) : Set (SpatialCoordinates d))) = 0) →
        ((Ls iQ).gamma.measure Vprime
          (centeredCube zprime rprime hrprime : Set (SpatialCoordinates d))).toReal = ∑ i : Fin m, Lam i))

end Paper
