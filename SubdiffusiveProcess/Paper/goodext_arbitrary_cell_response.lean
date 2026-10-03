module

public import SubdiffusiveProcess.Paper.goodext_response_of_root_minimizers
public import SubdiffusiveProcess.Paper.goodext_root_grid_coefficient_cap
public import SubdiffusiveProcess.Geometry.CubePowerComparison

@[expose] public section

/-! Arbitrary-cell response bound of `lem_goodext`: along one controlled subsequence carrying a
root-grid coefficient cap, every cell of the root cube has local response at most
`K r^{d-2+2α-η}`.  It asserts nothing about good cells. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

noncomputable section
namespace Paper

/-- Arbitrary-cell response bound of `lem_goodext`: along one controlled subsequence with a
root-grid coefficient cap, every cell of the root cube has a response `≤ K r^{d-2+2α-η}`. -/
theorem goodext_arbitrary_cell_response
    {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (X : Paper.in_extension d hd I)
    (Sob : Lane4.SobolevFoundationalInput d hd)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (S : ResponseSpace (centeredCube Qcentre Qside hQside))
    (hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
    (envs : ℕ → BilateralField d) (Ns : ℕ → ℕ) (hNs : StrictMono Ns)
    (tGrowth alpha beta etaCat etaGrid : ℝ) (halpha : 0 < alpha)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) (hba : beta ≤ alpha)
    (hEta : 1 + etaCat < 2 * alpha) (hetaCatGrid : etaCat ≤ etaGrid)
    (ARoot : aux_prop_conc_controlled_forms_analytic_controls d hd Qcentre Qside hQside S
      (fun n => Lane4.cutoffPositiveCoefficient M H (envs n) (Ns n) Qcentre hQside))
    (hRootCells : aux_prop_conc_mesh_cutoff_family_AllCellBounds Qcentre Qside hQside
      (fun n => cutoffCoefficient M H (envs n) (Ns n)) tGrowth alpha)
    (hRootReg : ∀ q : TriadicGridLabel d,
      ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
      ∀ b : weakSobolevGraph (triadicGridCell Qcentre Qside hQside q),
        ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (triadicGridCell Qcentre Qside hQside q : Set (SpatialCoordinates d))] phi) →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∃ V : SpatialCoordinates d → ℝ,
          ContinuousOn V (closure (triadicGridCell Qcentre Qside hQside q :
            Set (SpatialCoordinates d))) ∧
          ((dirichletMinimizer
            (killedResponseSpace (centeredCube_killedPoincare (triadicGridCenter Qcentre Qside q)
              (triadicGridSide_pos hQside q)))
            (Lane4.cutoffPositiveCoefficient M H (envs n) (Ns n)
              (triadicGridCenter Qcentre Qside q) (triadicGridSide_pos hQside q)) b).val.1 :
                SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                  (triadicGridCell Qcentre Qside hQside q : Set (SpatialCoordinates d))] V ∧
          Lane4.IsHolderOn alpha (closure (triadicGridCell Qcentre Qside hQside q :
            Set (SpatialCoordinates d))) V ∧
          Lane4.cAlphaNorm alpha (closure (triadicGridCell Qcentre Qside hQside q :
            Set (SpatialCoordinates d))) V ≤ C)
    (GN : ℕ → BilateralField d →
      DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
        DomainL2 (centeredCube Qcentre Qside hQside))
    (hGN : ∀ N omega f, GN N omega f =
      (responseSolution S (Lane4.cutoffPositiveCoefficient M H omega N Qcentre hQside)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (G : DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
      DomainL2 (centeredCube Qcentre Qside hQside))
    (hGconv : Tendsto (fun n => GN (Ns n) (envs n)) atTop (𝓝 G))
    (Form : DirichletForm.ClosedForm
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (hE : ∀ u, Form.energy u = limitFormEnergy G u)
    (hcont : ∀ f : DomainL2 (centeredCube Qcentre Qside hQside),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
        (G f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U ∧
        ∀ x ∈ frontier (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), U x = 0)
    (Gamma : DirichletForm.EnergyMeasure Form)
    (ellRoot : ℤ) (hQScale : Qside = (3 : ℝ) ^ ellRoot)
    (Kgrid : ℝ) (hKgrid : 0 ≤ Kgrid)
    (hKgridCap : ∀ (n k : ℕ) (idx : Fin d → ℤ), k ≤ Ns n →
      let wc : SpatialCoordinates d := fun i => Qcentre i + (3 : ℝ) ^ (-(k : ℤ)) * idx i
      let rc : ℝ := (3 : ℝ) ^ (-(k : ℤ))
      ∀ hc : 0 < rc,
      (centeredCube wc rc hc : Set (SpatialCoordinates d)) ⊆
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) →
      I.Lam wc rc hc (Lane4.cutoffPositiveCoefficient M H (envs n) (Ns n) wc hc)
        wc rc ((beta - 1 / 2) / 4) 2 +
        (I.lam wc rc hc (Lane4.cutoffPositiveCoefficient M H (envs n) (Ns n) wc hc)
          wc rc ((beta - 1 / 2) / 4) 2)⁻¹ ≤ Kgrid * rc ^ (-etaCat))
    (U : SpatialCoordinates d → ℝ)
    (hUc : ContinuousOn U (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (hUh : Lane4.IsHolderOn alpha
      (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) U)
    (hUb : ∀ x ∈ frontier (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), U x = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z' : SpatialCoordinates d) (r' : ℝ), 0 < r' →
      Metric.ball z' (r' / 2) ⊆ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) →
      (Gamma.continuousTraceValues
        (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
        (Metric.ball z' (r' / 2)) U).Nonempty ∧
      IsGLB (Gamma.continuousTraceValues
          (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
          (Metric.ball z' (r' / 2)) U)
        (sInf (Gamma.continuousTraceValues
          (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
          (Metric.ball z' (r' / 2)) U)) ∧
      sInf (Gamma.continuousTraceValues
          (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
          (Metric.ball z' (r' / 2)) U) ≤
        K * r' ^ ((d : ℝ) - 2 + 2 * alpha - etaGrid) := by
  have hRootCap := goodext_root_grid_coefficient_cap I M H envs Ns hNs Qcentre Qside hQside
    ellRoot hQScale beta etaCat Kgrid hKgridCap
  have hCoefRep (n : ℕ) := (Lane4.cutoffPositiveCoefficient_representative M H
    (envs n) (Ns n) Qcentre hQside).2.2.2
  have hRootEll (n : ℕ) : ∃ lo hi : ℝ, 0 < lo ∧
      ∀ x ∈ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
        lo ≤ cutoffCoefficient M H (envs n) (Ns n) x ∧
        cutoffCoefficient M H (envs n) (Ns n) x ≤ hi := by
    obtain ⟨lo, hi, hlo, hbounds⟩ := cutoffCoefficient_closedCube_bounds M H
      (envs n) (Ns n) Qcentre hQside
    exact ⟨lo, hi, hlo, fun x hx => hbounds x (centeredCube_subset_closedCube Qcentre hQside hx)⟩
  let aCell := fun (q : {q : TriadicGridLabel d // ellRoot.toNat ≤ q.1}) n =>
    Lane4.cutoffPositiveCoefficient M H (envs n) (Ns n)
      (triadicGridCenter Qcentre Qside q.val) (triadicGridSide_pos hQside q.val)
  have hCellRep : ∀ q n,
      (Lane4.cutoffPositiveCoefficient M H (envs n) (Ns n) Qcentre hQside).val =ᵐ[volume.restrict
          (triadicGridCell Qcentre Qside hQside q.val : Set (SpatialCoordinates d))]
        (aCell q n).val := by
    intro q n
    have hsub := triadicGridCell_subset Qcentre hQside q.val
    have hrrep : (Lane4.cutoffPositiveCoefficient M H (envs n) (Ns n) Qcentre hQside).val
        =ᵐ[volume.restrict (triadicGridCell Qcentre Qside hQside q.val : Set (SpatialCoordinates d))]
          cutoffCoefficient M H (envs n) (Ns n) :=
      ae_restrict_of_ae_restrict_of_subset hsub (hCoefRep n)
    have hcrep : (aCell q n).val
        =ᵐ[volume.restrict (triadicGridCell Qcentre Qside hQside q.val : Set (SpatialCoordinates d))]
          cutoffCoefficient M H (envs n) (Ns n) :=
      (Lane4.cutoffPositiveCoefficient_representative M H
        (envs n) (Ns n)
        (triadicGridCenter Qcentre Qside q.val) (triadicGridSide_pos hQside q.val)).2.2.2
    exact hrrep.trans hcrep.symm
  obtain ⟨K0, hK0, hResponse⟩ := goodext_response_of_root_minimizers hd I X Sob
    Qcentre Qside hQside S hS _ ARoot _
    (fun n => cutoffCoefficient_continuous M H (envs n) (Ns n))
    hRootEll hCoefRep tGrowth alpha halpha hRootCells
    (fun n => GN (Ns n) (envs n)) G
    (fun n f => hGN (Ns n) (envs n) f)
    hGconv Form hE hcont Gamma ellRoot.toNat beta etaCat Kgrid hbeta hba hEta hKgrid
    (fun q => triadicGridSide_le_one Qside ellRoot hQScale q.val q.property)
    U hUc hUh hUb aCell hCellRep (fun q => hRootReg q.val) hRootCap
  refine ⟨K0 * Qside ^ (etaGrid - etaCat),
    mul_nonneg hK0 (Real.rpow_nonneg hQside.le _), ?_⟩
  intro z' r' hr' hsub
  obtain ⟨hNonempty, hGLB, hBound⟩ := hResponse z' r' hr' hsub
  refine ⟨hNonempty, hGLB, hBound.trans ?_⟩
  have hPower := cube_rpow_exponent_le Qcentre z' Qside r' hQside hr' hsub
    ((d : ℝ) - 2 + 2 * alpha - etaCat) ((d : ℝ) - 2 + 2 * alpha - etaGrid)
    (by linarith only [hetaCatGrid])
  have hExp : ((d : ℝ) - 2 + 2 * alpha - etaCat) -
      ((d : ℝ) - 2 + 2 * alpha - etaGrid) = etaGrid - etaCat := by ring
  rw [hExp] at hPower
  exact (mul_le_mul_of_nonneg_left hPower hK0).trans_eq (by ring)

end Paper
