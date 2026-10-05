module

public import SubdiffusiveProcess.Paper.goodext_partition_trace_of_eventual_uniform_bank
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper
/-- A finite compatible bank with actual uniform cell limits and convergent cell
energies glues to a domain element with the exact sum bound. The cell bank and
its energy limits remain explicit inputs; this is not the density application. -/
theorem density_partition_energy_limit
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
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcont : ∀ f : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (G f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
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
    (b : ∀ _n i, PositiveCoefficient (centeredCube (cent i) (rad i) (hrad i)))
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
    (Lam Osc : Fin m → ℝ)
    (hEnergy : ∀ i, Tendsto (fun n => sobolevCoefficientForm (b n i) (u i n).val (u i n).val)
      atTop (𝓝 (Lam i)))
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
      E.form v v ≤ ∑ i, Lam i := by
  classical
  have hLam : ∀ i, 0 ≤ Lam i := fun i => ge_of_tendsto' (hEnergy i)
    (fun n => sobolevCoefficientForm_nonneg (b n i) (u i n).val)
  have happrox : ∀ eps : ℝ, 0 < eps →
      ∃ (v : DomainL2 (centeredCube z r hr)) (V : SpatialCoordinates d → ℝ),
        v ∈ E.domain ∧ ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
        (∀ i, EqOn V (Vcell i)
          (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))) ∧
        (∀ i, (∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)), V x = g x) ∧
          ∀ x ∈ closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)),
            |V x - g x| ≤ Osc i) ∧
        E.form v v ≤ (∑ i, Lam i) + (m : ℝ) * eps := by
    intro eps heps
    have hcap : ∀ i, 0 ≤ Lam i + eps := fun i => add_nonneg (hLam i) heps.le
    have hEvent : ∀ i, ∀ᶠ n in atTop,
        sobolevCoefficientForm (b n i) (u i n).val (u i n).val ≤ Lam i + eps := by
      intro i
      exact ((hEnergy i).eventually (eventually_lt_nhds (by linarith : Lam i < Lam i + eps))).mono
        (fun _ h => h.le)
    obtain ⟨v, V, hv, hVc, hVr, hVcell, hOscV, hcapV⟩ :=
      goodext_partition_trace_of_eventual_uniform_bank hd z r hr S hS a A c hc hell hrep
        t alpha ha hcell GN G hGN hConv E hE hcont Gamma m cent rad hrad hsub hdisj
        hcover hcoverAE g hg0 b hab u U hUc hUr hUt Vcell hlimit
        (fun i => Lam i + eps) Osc hcap hEvent hOsc
    have hBound := hcapV Set.univ isOpen_univ (fun i => Lam i + eps) hcap (fun _ _ => le_rfl)
    rw [Gamma.measure_univ v hv] at hBound
    refine ⟨v, V, hv, hVc, hVr, hVcell, hOscV, ?_⟩
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using hBound
  obtain ⟨v, V, hv, hVc, hVr, hVcell, hOscV, _hVenergy⟩ := happrox 1 (by norm_num)
  refine ⟨v, V, hv, hVc, hVr, hVcell, hOscV, ?_⟩
  apply le_of_forall_pos_le_add
  intro eps heps
  let small := eps / ((m : ℝ) + 1)
  have hsmall : 0 < small := div_pos heps (by positivity)
  obtain ⟨w, W, _hw, _hWc, hWr, hWcell, _hOscW, hWenergy⟩ := happrox small hsmall
  have hvw : v = w := by
    apply Lp.ext
    filter_upwards [hVr, hWr, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hxv hxw hxQ
    rw [hxv, hxw]
    have hxcl : x ∈ ⋃ i, closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) := by
      rw [hcover]
      exact subset_closure hxQ
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxcl
    exact (hVcell i hxi).trans (hWcell i hxi).symm
  rw [← hvw] at hWenergy
  have hscale : (m : ℝ) * small ≤ eps := by
    have hden : (m : ℝ) + 1 ≠ 0 := by positivity
    have heq : small * ((m : ℝ) + 1) = eps := by
      dsimp only [small]
      exact div_mul_cancel₀ _ hden
    nlinarith [hsmall]
  exact hWenergy.trans (add_le_add_right hscale _)
end SubdiffusiveProcess.Paper
