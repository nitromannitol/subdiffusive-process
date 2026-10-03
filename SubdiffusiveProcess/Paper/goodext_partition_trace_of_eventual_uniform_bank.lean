module

public import SubdiffusiveProcess.Paper.goodext_partition_trace_of_uniform_bank
public import SubdiffusiveProcess.Paper.goodext_compact_native_partition_bank
public import SubdiffusiveProcess.Paper.goodext_controlled_cluster_bank
public import SubdiffusiveProcess.Paper.prop_boundary
public import SubdiffusiveProcess.Sobolev.NativeCellEnergyBank
public import SubdiffusiveProcess.Sobolev.GradientEnergyMass
public import SubdiffusiveProcess.Sobolev.UniformCubeLimit
public import SubdiffusiveProcess.Sobolev.PartitionLocalEnergyCaps

@[expose] public section

/-! Eventual bounds for a finite compatible cubical response bank give a continuous
limiting witness with prescribed cell limits and open-set energy caps. The actual
minimizers and uniform limits remain explicit inputs. -/
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace Paper

/-- A finite cubical bank with prescribed uniform cell limits yields a glued trace and open-set energy caps. -/
theorem goodext_partition_trace_of_eventual_uniform_bank
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (c : ℕ → SpatialCoordinates d → ℝ) (hc : ∀ n, Continuous (c n))
    (hell : ∀ n, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), lam ≤ c n x ∧ c n x ≤ Lam)
    (hrep : ∀ n, (a n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] c n)
    (t alpha : ℝ) (ha : 0 < alpha)
    (hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr c t alpha)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
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
    (Gamma : DirichletForm.EnergyMeasure E)
    [NeZero d]
    (m : ℕ) (cent : Fin m → SpatialCoordinates d) (rad : Fin m → ℝ) (hrad : ∀ i, 0 < rad i)
    (hsub : ∀ i, (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hdisj : Pairwise (fun i j => Disjoint
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
      (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d))))
    (hcover : (⋃ i, closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))) =
      closure (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hcoverAE : (⋃ i, (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))
      =ᵐ[volume] (centeredCube z r hr : Set (SpatialCoordinates d)))
    (g : SpatialCoordinates d → ℝ)
    (hg0 : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), g x = 0)
    (b : ∀ n i, PositiveCoefficient (centeredCube (cent i) (rad i) (hrad i)))
    (hab : ∀ n i, (a n).val =ᵐ[volume.restrict
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))] (b n i).val)
    (u : ∀ i, ℕ → weakSobolevGraph (centeredCube (cent i) (rad i) (hrad i)))
    (U : Fin m → ℕ → SpatialCoordinates d → ℝ)
    (hUc : ∀ i n, ContinuousOn (U i n)
      (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))))
    (hUr : ∀ i n, ((u i n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))] U i n)
    (hUt : ∀ i n, ∀ x ∈ frontier
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)), U i n x = g x)
    (Vcell : Fin m → SpatialCoordinates d → ℝ)
    (hlimit : ∀ i, TendstoUniformlyOn (U i) (Vcell i) atTop
      (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))))
    (Ecell Osc : Fin m → ℝ) (hEc : ∀ i, 0 ≤ Ecell i)
    (hEnergy : ∀ i, ∀ᶠ n in atTop, sobolevCoefficientForm (b n i) (u i n).val (u i n).val ≤ Ecell i)
    (hOsc : ∀ i n x, x ∈ closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) →
      |U i n x - g x| ≤ Osc i) :
    ∃ (v : DomainL2 (centeredCube z r hr)) (V : SpatialCoordinates d → ℝ),
      v ∈ E.domain ∧ ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
      (∀ i, EqOn V (Vcell i)
        (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))) ∧
      (∀ i, (∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)), V x = g x) ∧
        ∀ x ∈ closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)),
          |V x - g x| ≤ Osc i) ∧
      ∀ (O : Set (SpatialCoordinates d)), IsOpen O → ∀ (cap : Fin m → ℝ),
        (∀ i, 0 ≤ cap i) →
        (∀ i, ((centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) ∩ O).Nonempty →
          Ecell i ≤ cap i) →
        (Gamma.measure v O).toReal ≤ ∑ i, cap i := by
  classical
  have hEventually : ∀ᶠ n in atTop, ∀ i,
      sobolevCoefficientForm (b n i) (u i n).val (u i n).val ≤ Ecell i :=
    eventually_all.mpr hEnergy
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hEventually
  let rho : ℕ → ℕ := fun n => n + N0
  have hrho : StrictMono rho := strictMono_id.add_const N0
  have hCell : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
      (fun n => c (rho n)) t alpha := by
    intro J hJ theta htheta thetaH hthetaH k
    obtain ⟨E0, Gr, Ho, hE0, hGr, hHo, hbound⟩ := hcell J hJ theta htheta thetaH hthetaH k
    exact ⟨E0, Gr, Ho, hE0, hGr, hHo, fun n => hbound (rho n)⟩
  exact goodext_partition_trace_of_uniform_bank hd z r hr S hS
    (fun n => a (rho n)) (aux_prop_conc_controlled_forms_controls_reindex A rho)
    (fun n => c (rho n)) (fun n => hc (rho n)) (fun n => hell (rho n))
    (fun n => hrep (rho n)) t alpha ha hCell
    (fun n => GN (rho n)) G (fun n => hGN (rho n)) (hConv.comp hrho.tendsto_atTop)
    E hE hcont Gamma m cent rad hrad hsub hdisj hcover hcoverAE g hg0
    (fun n => b (rho n)) (fun n => hab (rho n))
    (fun i n => u i (rho n)) (fun i n => U i (rho n))
    (fun i n => hUc i (rho n)) (fun i n => hUr i (rho n)) (fun i n => hUt i (rho n))
    Vcell (fun i => (hlimit i).seq_tendstoUniformlyOn rho hrho.tendsto_atTop)
    Ecell Osc hEc (fun i n => hN0 (rho n) (Nat.le_add_left N0 n) i)
    (fun i n => hOsc i (rho n))

end Paper
