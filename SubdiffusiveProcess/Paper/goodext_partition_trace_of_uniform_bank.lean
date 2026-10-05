module

public import SubdiffusiveProcess.Paper.goodext_compact_native_partition_bank
public import SubdiffusiveProcess.Paper.goodext_controlled_cluster_bank
public import SubdiffusiveProcess.Paper.prop_boundary
public import SubdiffusiveProcess.Sobolev.NativeCellEnergyBank
public import SubdiffusiveProcess.Sobolev.GradientEnergyMass
public import SubdiffusiveProcess.Sobolev.UniformCubeLimit
public import SubdiffusiveProcess.Sobolev.PartitionLocalEnergyCaps

@[expose] public section

/-! A finite compatible cubical response bank gives a continuous limiting witness,
cellwise trace and oscillation control, and open-set energy caps. This theorem does
not assign zero limiting energy to partition interfaces. -/
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A finite cubical bank with prescribed uniform cell limits yields a glued trace and open-set energy caps. -/
theorem goodext_partition_trace_of_uniform_bank
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
    (Ecell Osc : Fin m → ℝ) (hEc : ∀ i, 0 ≤ Ecell i)
    (hEnergy : ∀ i n, sobolevCoefficientForm (b n i) (u i n).val (u i n).val ≤ Ecell i)
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
  have hcompact : ∀ i, ∀ sigma : ℕ → ℕ, StrictMono sigma →
      ∃ tau : ℕ → ℕ, StrictMono tau ∧ ∃ V : SpatialCoordinates d → ℝ,
        TendstoUniformlyOn (fun n => U i (sigma (tau n))) V atTop
          (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))) := by
    intro i sigma hsigma
    refine ⟨id, strictMono_id, Vcell i, ?_⟩
    simpa only [id_eq] using
      (hlimit i).seq_tendstoUniformlyOn sigma hsigma.tendsto_atTop
  obtain ⟨w, rho, V, v, hrho, hVcont, hvrep, hL2, hUniform, hTrace, hw⟩ :=
    goodext_compact_native_partition_bank z r hr m cent rad hrad hsub hdisj hcover g hg0
      u U hUc hUr hUt hcompact
  let wS : ℕ → S.space := fun n =>
    ⟨sobolevDataOfH1 (w (rho n)).toH1Function,
      hS.symm ▸ sobolevDataOfH1_mem_killed (w (rho n))⟩
  let muN : ℕ → Measure (SpatialCoordinates d) := fun n =>
    gradientEnergyMeasure (a (rho n)) (sobolevGradient (wS n).val)
  have hMuEq (n : ℕ) : muN n = gradientEnergyMeasure (a (rho n))
      (sobolevGradient (sobolevDataOfH1 (w (rho n)).toH1Function)) := by
    rfl
  have hBank (n : ℕ) := native_cell_energy_bank
      (fun i : Fin m => centeredCube (cent i) (rad i) (hrad i))
      (fun i => hsub i) hdisj hcoverAE (a (rho n)) (fun i => b (rho n) i) (hab (rho n))
      (w (rho n)).toH1Function (fun i => u i (rho n))
      (fun i => (hw (rho n)).2 i |>.2) Ecell hEc (fun i => hEnergy i (rho n))
  have hMass : ∀ n, muN n Set.univ ≤ ENNReal.ofReal (∑ i, Ecell i) := by
    intro n
    rw [hMuEq n]
    exact (hBank n).2.1
  have hLocal : ∀ n i,
      muN n (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) ≤
        ENNReal.ofReal (Ecell i) := by
    intro n i
    rw [hMuEq n]
    exact (hBank n).1 i
  have hSupport : ∀ n, muN n (closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ = 0 := by
    intro n
    rw [hMuEq n]
    exact (hBank n).2.2.1
  have hBound : ∀ n, responseForm S (a (rho n)) (wS n) (wS n) ≤ ∑ i, Ecell i := by
    intro n
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hMass n)
    rw [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => hEc i))] at hreal
    change (gradientEnergyMeasure (a (rho n))
      (sobolevGradient (wS n).val) Set.univ).toReal ≤ _ at hreal
    rw [gradientEnergyMeasure_univ_toReal] at hreal
    change sobolevCoefficientForm (a (rho n)) (wS n).val (wS n).val ≤ _
    exact hreal
  obtain ⟨nu, sigma, hsigma, hnufin, hnusupp, hConvMu⟩ :=
    aux_prop_boundary_weak_cluster (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
      (centeredCube_isBounded z hr).isCompact_closure muN (∑ i, Ecell i) hSupport hMass
  obtain ⟨hv, hdominate⟩ :=
    goodext_controlled_cluster_bank hd z r hr S hS a A c hc hell hrep
      t alpha ha hcell GN G hGN hConv E hE hcont Gamma
      rho hrho v wS (∑ i, Ecell i) nu sigma hnufin hnusupp hsigma
      (by simpa only [wS] using hL2) hBound
      (by
        intro phi hphi
        simpa only [muN] using hConvMu phi hphi)
  have hlim : TendstoUniformly
      (fun n (x : closure (centeredCube z r hr : Set (SpatialCoordinates d))) =>
        (w (rho n)).toFun x.val)
      (fun x => V x.val) atTop := by
    rw [Metric.tendstoUniformly_iff]
    rw [Metric.tendstoUniformlyOn_iff] at hUniform
    intro ε hε
    filter_upwards [hUniform ε hε] with n hn x
    exact hn x.val x.property
  refine ⟨v, V, hv, hVcont, hvrep, ?_, ?_, ?_⟩
  · intro i x hx
    have hxQ : x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      closure_mono (hsub i) hx
    have hroot : Tendsto (fun n => (w (rho n)).toFun x) atTop (𝓝 (V x)) :=
      hlim.tendsto_at ⟨x, hxQ⟩
    have hcellUniform : TendstoUniformlyOn (fun n => U i (rho n)) (Vcell i) atTop
        (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))) :=
      (hlimit i).seq_tendstoUniformlyOn rho hrho.tendsto_atTop
    have hcell : Tendsto (fun n => U i (rho n) x) atTop (𝓝 (Vcell i x)) :=
      hcellUniform.tendsto_at hx
    have hrootCell : Tendsto (fun n => (w (rho n)).toFun x) atTop (𝓝 (Vcell i x)) := by
      apply hcell.congr'
      filter_upwards [] with n
      exact (((hw (rho n)).2 i).1 hx).symm
    exact tendsto_nhds_unique hroot hrootCell
  · intro i
    refine ⟨hTrace i, ?_⟩
    intro x hx
    have hxQ : x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      closure_mono (hsub i) hx
    have hpoint : Tendsto (fun n => U i (rho n) x) atTop (𝓝 (V x)) := by
      apply (hlim.tendsto_at ⟨x, hxQ⟩).congr'
      filter_upwards [] with n
      exact ((hw (rho n)).2 i).1 hx
    exact le_of_tendsto' ((hpoint.sub_const (g x)).abs)
      (fun n => hOsc i (rho n) x hx)
  · intro O hO cap hcap hmeet
    have hOpenBound : ∀ n,
        muN (sigma n) O ≤ ENNReal.ofReal (∑ i, cap i) := by
      intro n
      let f : SpatialCoordinates d → ENNReal := fun x =>
        ENNReal.ofReal ((a (rho (sigma n))).val x *
          ∑ j : Fin d, (sobolevGradient (wS (sigma n)).val j x) ^ 2)
      have hcellBound : ∀ i,
          ((centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) ∩ O).Nonempty →
          ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity f)
              (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) ≤
            ENNReal.ofReal (cap i) := by
        intro i hi
        have hloc := hLocal (sigma n) i
        have hcap_i := hmeet i hi
        change gradientEnergyMeasure (a (rho (sigma n)))
          (sobolevGradient (wS (sigma n)).val)
          (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) ≤ _ at hloc
        rw [gradientEnergyMeasure] at hloc
        change _ ≤ ENNReal.ofReal (cap i)
        exact hloc.trans (ENNReal.ofReal_le_ofReal hcap_i)
      have hsum := SubdiffusiveProcess.withDensity_set_le_sum_of_partition_caps
        volume (centeredCube z r hr : Set (SpatialCoordinates d))
        (fun i : Fin m => (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))
        hsub (fun i => (centeredCube (cent i) (rad i) (hrad i)).isOpen.measurableSet)
        hdisj hcoverAE f O hO.measurableSet cap hcap hcellBound
      simpa only [muN, gradientEnergyMeasure, f] using hsum
    have hnuO : nu O ≤ ENNReal.ofReal (∑ i, cap i) := aux_prop_boundary_open_le
      (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
      (fun n => muN (sigma n)) nu
      (fun n => (hMass (sigma n)).trans_lt ENNReal.ofReal_lt_top)
      hnufin hConvMu O hO (ENNReal.ofReal (∑ i, cap i)) hOpenBound
    have hGammaO := (hdominate O hO.measurableSet).trans hnuO
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hGammaO
    rw [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => hcap i))] at hreal
    exact hreal

end SubdiffusiveProcess.Paper
