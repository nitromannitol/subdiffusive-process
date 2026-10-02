import SubdiffusiveProcess.Paper.density_cutoff_partition_gluing

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- Closure of the finite-partition gluing over shrinking meshes: if for every mesh and tolerance the bank
admits a finite partition of the killed cube with total cost at most `Cglob + eps`, then the glued functions
converge uniformly to the boundary datum and their energies are eventually at most `Cglob + eps`. -/
theorem density_glue_sequence
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
      (Cglob : ℝ)
      (hPart : ∀ mesh : ℝ, 0 < mesh → ∀ eps : ℝ, 0 < eps →
        ∃ (total : ℕ) (q : Fin total → Bank), (∀ i, side (q i) ≤ mesh) ∧
          Pairwise (fun i j => Disjoint (cube (q i) : Set (SpatialCoordinates d)) (cube (q j) : Set (SpatialCoordinates d))) ∧
          (⋃ i, closure (cube (q i) : Set (SpatialCoordinates d))) = closure (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
          ((⋃ i, (cube (q i) : Set (SpatialCoordinates d))) =ᵐ[volume] (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          ∑ i, cost (q i) ≤ Cglob + eps),
    ∃ (v : ℕ → DomainL2 (centeredCube z r hr)) (V : ℕ → SpatialCoordinates d → ℝ),
      (∀ J, v J ∈ E.domain) ∧
      (∀ J, ContinuousOn (V J) (closure (centeredCube z r hr : Set (SpatialCoordinates d)))) ∧
      (∀ J, (v J : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V J) ∧
      ∀ eps : ℝ, 0 < eps → ∃ J0 : ℕ, ∀ J ≥ J0,
        (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), |V J x - g x| ≤ eps) ∧
        E.form (v J) (v J) ≤ Cglob + eps := by
  intro Bank centre side cube coeff g hg0 Osc hOsc uN VN Vcell cost hBank Cglob hPart
  have hmesh : ∀ J : ℕ, ∃ m : ℝ, 0 < m ∧ Osc * m ^ alpha ≤ 1 / ((J : ℝ) + 1) := by
    intro J
    have hJ : (0 : ℝ) < (J : ℝ) + 1 := by positivity
    refine ⟨((1 / ((J : ℝ) + 1)) / (Osc + 1)) ^ (1 / alpha), by positivity, ?_⟩
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel ha.ne', Real.rpow_one]
    have h1 : 0 < Osc + 1 := by linarith
    rw [mul_div_assoc', div_le_iff₀ h1]
    have : 0 ≤ 1 / ((J : ℝ) + 1) := by positivity
    nlinarith
  choose m hm0 hmOsc using hmesh
  have hex := fun J : ℕ => hPart (m J) (hm0 J) (1 / ((J : ℝ) + 1)) (by positivity)
  choose total q hqmesh hqdisj hqcover hqAE hqsum using hex
  have hglue := fun J : ℕ =>
    density_cutoff_partition_gluing hd M H env phi z r hr S hS A t alpha ha hcell GN G hGN hConv E hE
      hcont Gamma g hg0 Osc hOsc uN VN Vcell cost hBank (total J) (q J) (m J) (hqmesh J) (hqdisj J)
      (hqcover J) (hqAE J)
  choose v V hv hVc hVr hVosc hVE using hglue
  refine ⟨v, V, hv, hVc, hVr, ?_⟩
  intro eps heps
  obtain ⟨J0, hJ0⟩ := exists_nat_one_div_lt heps
  have hle : ∀ J ≥ J0, 1 / ((J : ℝ) + 1) ≤ eps := by
    intro J hJ
    refine le_trans ?_ hJ0.le
    apply one_div_le_one_div_of_le (by positivity)
    have : (J0 : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  refine ⟨J0, fun J hJ => ⟨fun x hx => ?_, ?_⟩⟩
  · exact (hVosc J x hx).trans ((hmOsc J).trans (hle J hJ))
  · exact (hVE J).trans (by linarith [hqsum J, hle J hJ])
end Paper
