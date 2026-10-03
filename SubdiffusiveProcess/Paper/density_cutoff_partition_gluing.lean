module

public import SubdiffusiveProcess.Paper.density_partition_energy_limit
public import SubdiffusiveProcess.Paper.density_full_grid
public import SubdiffusiveProcess.Lane4.CutoffCoefficientRepresentative
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- Glue a finite partition selected from the actual cutoff harmonic bank.
Coefficient compatibility follows from their common literal cutoff field.
The cell oscillation bounds become a uniform error controlled by the mesh. -/
theorem density_cutoff_partition_gluing
    {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (env : ℕ → BilateralField d) (phi : ℕ → ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S
      (fun n => cutoffPositiveCoefficient M H (env n) (phi n) z hr))
    (t alpha : ℝ) (ha : 0 < alpha)
    (hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
      (fun n => cutoffCoefficient M H (env n) (phi n)) t alpha)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (cutoffPositiveCoefficient M H (env n) (phi n) z hr)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : DirichletForm.ClosedForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcont : ∀ f : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (G f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0)
    (Gamma : DirichletForm.EnergyMeasure E) :
    let Bank := aux_density_full_grid_cells z r hr
    let centre := fun q : Bank => aux_goodext_admissible_grid_centre z q.val
    let side := fun q : Bank => (3 : ℝ) ^ (-(q.val.1 : ℤ))
    let cube := fun q : Bank => centeredCube (centre q) (side q) (zpow_pos (by norm_num) _)
    let coeff := fun q n => cutoffPositiveCoefficient M H (env n) (phi n) (centre q)
      (show 0 < side q from zpow_pos (by norm_num) _)
    ∀ (g : SpatialCoordinates d → ℝ)
      (hg0 : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), g x = 0)
      (Osc : ℝ) (hOsc : 0 ≤ Osc)
      (uN : ∀ q, ℕ → weakSobolevGraph (cube q))
      (VN : Bank → ℕ → SpatialCoordinates d → ℝ)
      (Vcell : Bank → SpatialCoordinates d → ℝ) (cost : Bank → ℝ)
      (hBank : ∀ q,
        (∀ n, ContinuousOn (VN q n) (closure (cube q : Set (SpatialCoordinates d))) ∧
          ((uN q n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (cube q : Set (SpatialCoordinates d))] VN q n ∧
          (∀ x ∈ frontier (cube q : Set (SpatialCoordinates d)), VN q n x = g x) ∧
          ∀ x ∈ closure (cube q : Set (SpatialCoordinates d)), |VN q n x - g x| ≤ Osc * side q ^ alpha) ∧
        TendstoUniformlyOn (VN q) (Vcell q) atTop (closure (cube q : Set (SpatialCoordinates d))) ∧
        Tendsto (fun n => sobolevCoefficientForm (coeff q n) (uN q n).val (uN q n).val)
          atTop (𝓝 (cost q)))
      (total : ℕ) (q : Fin total → Bank) (mesh : ℝ) (hmesh : ∀ i, side (q i) ≤ mesh)
      (hdisj : Pairwise (fun i j => Disjoint (cube (q i) : Set (SpatialCoordinates d)) (cube (q j) : Set (SpatialCoordinates d))))
      (hcover : (⋃ i, closure (cube (q i) : Set (SpatialCoordinates d))) = closure (centeredCube z r hr : Set (SpatialCoordinates d)))
      (hcoverAE : (⋃ i, (cube (q i) : Set (SpatialCoordinates d))) =ᵐ[volume] (centeredCube z r hr : Set (SpatialCoordinates d))),
    ∃ (v : DomainL2 (centeredCube z r hr)) (V : SpatialCoordinates d → ℝ),
      v ∈ E.domain ∧ ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
      (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), |V x - g x| ≤ Osc * mesh ^ alpha) ∧
      E.form v v ≤ ∑ i, cost (q i) := by
  classical
  intro Bank centre side cube coeff g hg0 Osc hOsc uN VN Vcell cost hBank total q mesh hmesh hdisj hcover hcoverAE
  let a := fun n => cutoffPositiveCoefficient M H (env n) (phi n) z hr
  let c := fun n => cutoffCoefficient M H (env n) (phi n)
  have hrep : ∀ n, (a n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] c n :=
    fun n => (cutoffPositiveCoefficient_representative M H (env n) (phi n) z hr).2.2.2
  have hell : ∀ n, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), lam ≤ c n x ∧ c n x ≤ Lam := by
    intro n
    obtain ⟨lam, Lam, hlam, hbounds⟩ := cutoffCoefficient_closedCube_bounds M H (env n) (phi n) z hr
    exact ⟨lam, Lam, hlam, fun x hx => hbounds x (centeredCube_subset_closedCube z hr hx)⟩
  have hab : ∀ n i, (a n).val =ᵐ[volume.restrict (cube (q i) : Set (SpatialCoordinates d))] (coeff (q i) n).val := by
    intro n i
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (q i).property (hrep n),
      (cutoffPositiveCoefficient_representative M H (env n) (phi n) (centre (q i))
        (show 0 < side (q i) from zpow_pos (by norm_num) _)).2.2.2] with x hxQ hxq
    exact hxQ.trans hxq.symm
  have h := density_partition_energy_limit hd z r hr S hS a A c
    (fun n => cutoffCoefficient_continuous M H (env n) (phi n)) hell hrep
    t alpha ha hcell GN G hGN hConv E hE hcont Gamma total
    (fun i => centre (q i)) (fun i => side (q i)) (fun _ => zpow_pos (by norm_num) _)
    (fun i => (q i).property) hdisj hcover hcoverAE g hg0
    (fun n i => coeff (q i) n) hab (fun i => uN (q i)) (fun i => VN (q i))
    (fun i n => ((hBank (q i)).1 n).1) (fun i n => ((hBank (q i)).1 n).2.1)
    (fun i n => ((hBank (q i)).1 n).2.2.1) (fun i => Vcell (q i))
    (fun i => (hBank (q i)).2.1) (fun i => cost (q i)) (fun i => Osc * side (q i) ^ alpha)
    (fun i => (hBank (q i)).2.2) (fun i n => ((hBank (q i)).1 n).2.2.2)
  obtain ⟨v, V, hv, hVc, hVr, _hVcell, hVosc, hEnergy⟩ := h
  refine ⟨v, V, hv, hVc, hVr, ?_, hEnergy⟩
  intro x hx
  have hx' : x ∈ ⋃ i, closure (cube (q i) : Set (SpatialCoordinates d)) := hcover.symm ▸ hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx'
  exact ((hVosc i).2 x hi).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 3) _)) (hmesh i) ha.le) hOsc)
end Paper
