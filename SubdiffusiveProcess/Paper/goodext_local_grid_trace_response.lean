import SubdiffusiveProcess.Sobolev.NativeTraceEnergyExtension
import SubdiffusiveProcess.Paper.goodext_compact_native_cell_bank
import SubdiffusiveProcess.Paper.goodext_controlled_cluster_bank
import SubdiffusiveProcess.Paper.prop_boundary
import SubdiffusiveProcess.Sobolev.NativeCellEnergyBank
import SubdiffusiveProcess.Sobolev.CoefficientRestriction
import SubdiffusiveProcess.Sobolev.ContinuousZeroExtension
import SubdiffusiveProcess.Sobolev.ContinuousNativeRepresentative
import SubdiffusiveProcess.Sobolev.UniformCubeLimit
import SubdiffusiveProcess.Sobolev.GradientEnergyMass

/-! A compatible finite grid of continuous cell banks yields a domain element
of the prescribed limiting form and preserves each cell's separate energy bound.
-/
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace Paper

/-- A compact local cell bank extends to a continuous limiting-form witness on the ambient cube. -/
theorem goodext_local_grid_trace_response
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
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (hPsub : (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (J : ℕ)
    (g : SpatialCoordinates d → ℝ)
    (hg0 : ∀ x ∈ frontier (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)), g x = 0)
    (b : ∀ n : ℕ, ∀ k : OddGridIndex d (triadicHalf J),
      PositiveCoefficient (oddGridCell z0 r0 hr0 (triadicHalf J) k))
    (hab : ∀ n k, (a n).val =ᵐ[volume.restrict
      (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))] (b n k).val)
    (u : ∀ k : OddGridIndex d (triadicHalf J), ℕ →
      weakSobolevGraph (oddGridCell z0 r0 hr0 (triadicHalf J) k))
    (U : OddGridIndex d (triadicHalf J) → ℕ → SpatialCoordinates d → ℝ)
    (hUc : ∀ k n, ContinuousOn (U k n)
      (closure (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))))
    (hUr : ∀ k n, ((u k n).val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))] U k n)
    (hUt : ∀ k n, ∀ x ∈ frontier
      (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d)), U k n x = g x)
    (hcompact : ∀ k, ∀ sigma : ℕ → ℕ, StrictMono sigma →
      ∃ tau : ℕ → ℕ, StrictMono tau ∧ ∃ V : SpatialCoordinates d → ℝ,
        TendstoUniformlyOn (fun n => U k (sigma (tau n))) V atTop
          (closure (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))))
    (Ecell : OddGridIndex d (triadicHalf J) → ℝ) (hEc : ∀ k, 0 ≤ Ecell k)
    (hEnergy : ∀ k n, sobolevCoefficientForm (b n k) (u k n).val (u k n).val ≤ Ecell k) :
    ∃ (v : DomainL2 (centeredCube z r hr)) (V : SpatialCoordinates d → ℝ),
      v ∈ E.domain ∧ ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
      ∀ k, (∀ x ∈ frontier (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d)),
        V x = g x) ∧
        (Gamma.measure v (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))).toReal ≤ Ecell k := by
  classical
  let P := centeredCube z0 r0 hr0
  let Q := centeredCube z r hr
  have hPQ : P ≤ Q := by
    change (P : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d))
    exact hPsub
  let aP : ℕ → PositiveCoefficient P := fun n =>
    positiveCoefficientRestrict hPQ (a n)
  have hAP (n : ℕ) : (a n).val =ᵐ[volume.restrict (P : Set (SpatialCoordinates d))]
      (aP n).val := (positiveCoefficientRestrict_coeFn hPQ (a n)).symm
  have habP (n : ℕ) (k : OddGridIndex d (triadicHalf J)) :
      ((aP n).val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))] (b n k).val := by
    have hcoeff := positiveCoefficientRestrict_coeFn hPQ (a n)
    have hcoeffCell : ((aP n).val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d))] (a n).val := by
      exact ae_restrict_of_ae_restrict_of_subset
        (oddGridCell_subset z0 hr0 (triadicHalf J) k) hcoeff
    exact hcoeffCell.trans (hab n k)
  obtain ⟨wP, rho, Vp, vP, hrho, hVpc, hvpr, hL2P, hUniformP, hTraceP, hwP⟩ :=
    goodext_compact_native_cell_bank z0 r0 hr0 J g hg0 u U hUc hUr hUt hcompact
  have hPfrontier_zero (n : ℕ) :
      ∀ x ∈ frontier (P : Set (SpatialCoordinates d)),
        (wP n).toH1Function.toFun x = 0 := by
    intro x hxfront
    have hxclose : x ∈ closure (P : Set (SpatialCoordinates d)) :=
      frontier_subset_closure hxfront
    have hxcomp : x ∈ closure ((P : Set (SpatialCoordinates d))ᶜ) := by
      rw [frontier_eq_closure_inter_closure] at hxfront
      exact hxfront.2
    have hxnotP : x ∉ (P : Set (SpatialCoordinates d)) := by
      rw [closure_compl, P.isOpen.interior_eq] at hxcomp
      exact hxcomp
    have hxunion : x ∈ ⋃ k : OddGridIndex d (triadicHalf J),
        closure (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d)) := by
      rw [oddGridCell_closure_iUnion_eq_closure_centeredCube z0 hr0 (triadicHalf J)]
      exact hxclose
    obtain ⟨k, hxcell⟩ := Set.mem_iUnion.mp hxunion
    have hxnotcell : x ∉ (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d)) := by
      intro hx
      exact hxnotP ((oddGridCell_subset z0 hr0 (triadicHalf J) k) hx)
    have hxcellfront : x ∈ frontier
        (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d)) := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨hxcell, subset_closure hxnotcell⟩
    calc
      (wP n).toH1Function.toFun x = U k n x := ((hwP n).2 k).1 hxcell
      _ = g x := hUt k n x hxcellfront
      _ = 0 := hg0 x hxfront
  have hVpfrontier_zero :
      ∀ x ∈ frontier (P : Set (SpatialCoordinates d)), Vp x = 0 := by
    intro x hxfront
    have hxclose : x ∈ closure (P : Set (SpatialCoordinates d)) :=
      frontier_subset_closure hxfront
    have hxcomp : x ∈ closure ((P : Set (SpatialCoordinates d))ᶜ) := by
      rw [frontier_eq_closure_inter_closure] at hxfront
      exact hxfront.2
    have hxnotP : x ∉ (P : Set (SpatialCoordinates d)) := by
      rw [closure_compl, P.isOpen.interior_eq] at hxcomp
      exact hxcomp
    have hxunion : x ∈ ⋃ k : OddGridIndex d (triadicHalf J),
        closure (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d)) := by
      rw [oddGridCell_closure_iUnion_eq_closure_centeredCube z0 hr0 (triadicHalf J)]
      exact hxclose
    obtain ⟨k, hxcell⟩ := Set.mem_iUnion.mp hxunion
    have hxnotcell : x ∉ (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d)) := by
      intro hx
      exact hxnotP ((oddGridCell_subset z0 hr0 (triadicHalf J) k) hx)
    have hxcellfront : x ∈ frontier
        (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d)) := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨hxcell, subset_closure hxnotcell⟩
    exact (hTraceP k x hxcellfront).trans (hg0 x hxfront)
  obtain ⟨VQ, hVQc, hVQrep, hVQzero⟩ :=
    continuous_zero_extension_of_frontier_zero P vP Vp hVpc hvpr hVpfrontier_zero
  have hVQcP : ContinuousOn VQ (closure (P : Set (SpatialCoordinates d))) :=
    hVQc.continuousOn.mono (subset_univ _)
  have hVQaeVp : VQ =ᵐ[volume.restrict (P : Set (SpatialCoordinates d))] Vp :=
    hVQrep.symm.trans hvpr
  have hVQeqVp : EqOn VQ Vp (closure (P : Set (SpatialCoordinates d))) :=
    eqOn_closure_of_ae_eq_restrict P.isOpen hVQcP hVpc hVQaeVp
  have hext (n : ℕ) : ∃ w : H10Function (Q : Set (SpatialCoordinates d)),
      Continuous w.toH1Function.toFun ∧
      EqOn w.toH1Function.toFun (wP (rho n)).toH1Function.toFun
        (closure (P : Set (SpatialCoordinates d))) ∧
      (∀ x ∉ (P : Set (SpatialCoordinates d)), w.toH1Function.toFun x = 0) ∧
      gradientEnergyMeasure (a (rho n))
          (sobolevGradient (sobolevDataOfH1 w.toH1Function)) =
        gradientEnergyMeasure (aP (rho n))
          (sobolevGradient (sobolevDataOfH1 (wP (rho n)).toH1Function)) := by
    exact exists_continuous_native_energy_extension hPQ (a (rho n)) (aP (rho n))
      (hAP (rho n)) (wP (rho n)) (hwP (rho n)).1
      (hPfrontier_zero (rho n))
  let wQ : ℕ → H10Function (Q : Set (SpatialCoordinates d)) :=
    fun n => Classical.choose (hext n)
  have hwQ n := Classical.choose_spec (hext n)
  let wS : ℕ → S.space := fun n =>
    ⟨sobolevDataOfH1 (wQ n).toH1Function,
      hS.symm ▸ sobolevDataOfH1_mem_killed (wQ n)⟩
  let muN : ℕ → Measure (SpatialCoordinates d) := fun n =>
    gradientEnergyMeasure (a (rho n)) (sobolevGradient (wS n).val)
  let muP : ℕ → Measure (SpatialCoordinates d) := fun n =>
    gradientEnergyMeasure (aP (rho n))
      (sobolevGradient (sobolevDataOfH1 (wP (rho n)).toH1Function))
  have hMuEq (n : ℕ) : muN n = muP n := by
    change gradientEnergyMeasure (a (rho n))
        (sobolevGradient (sobolevDataOfH1 (wQ n).toH1Function)) = _
    exact (hwQ n).2.2.2
  have hBankP (n : ℕ) := native_cell_energy_bank
    (fun k : OddGridIndex d (triadicHalf J) =>
      oddGridCell z0 r0 hr0 (triadicHalf J) k)
    (fun k => oddGridCell_subset z0 hr0 (triadicHalf J) k)
    (oddGridCell_pairwiseDisjoint z0 hr0 (triadicHalf J))
    (oddGrid_union_ae_eq z0 hr0 (triadicHalf J))
    (aP (rho n)) (b (rho n)) (habP (rho n))
    (wP (rho n)).toH1Function (fun k => u k (rho n))
    (fun k => ((hwP (rho n)).2 k).2) Ecell hEc (fun k => hEnergy k (rho n))
  have hMass : ∀ n, muN n Set.univ ≤ ENNReal.ofReal (∑ k, Ecell k) := by
    intro n
    rw [hMuEq n]
    exact (hBankP n).2.1
  have hLocal : ∀ n k,
      muN n (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d)) ≤
        ENNReal.ofReal (Ecell k) := by
    intro n k
    rw [hMuEq n]
    exact (hBankP n).1 k
  have hPcQ : closure (P : Set (SpatialCoordinates d)) ⊆
      closure (Q : Set (SpatialCoordinates d)) := closure_mono hPsub
  have hSupport : ∀ n, muN n (closure (Q : Set (SpatialCoordinates d)))ᶜ = 0 := by
    intro n
    rw [hMuEq n]
    apply measure_mono_null (t := (closure (P : Set (SpatialCoordinates d)))ᶜ)
    · intro x hx hxP
      exact hx (hPcQ hxP)
    · exact (hBankP n).2.2.1
  have hBound : ∀ n, responseForm S (a (rho n)) (wS n) (wS n) ≤ ∑ k, Ecell k := by
    intro n
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hMass n)
    rw [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun k _ => hEc k))] at hreal
    change (gradientEnergyMeasure (a (rho n))
      (sobolevGradient (wS n).val) Set.univ).toReal ≤ _ at hreal
    rw [gradientEnergyMeasure_univ_toReal] at hreal
    change sobolevCoefficientForm (a (rho n)) (wS n).val (wS n).val ≤ _
    exact hreal
  let VQc : C(closure (Q : Set (SpatialCoordinates d)), ℝ) :=
    ⟨fun x => VQ x, hVQc.comp continuous_subtype_val⟩
  obtain ⟨vQ, Vrep, hVrepcont, hvQrep, hVrepEq⟩ :=
    exists_cubeL2_of_continuous_closedCube z hr VQc
  have hVrepVQ (x : SpatialCoordinates d)
      (hx : x ∈ closure (Q : Set (SpatialCoordinates d))) : Vrep x = VQ x := by
    simpa only [VQc] using hVrepEq x hx
  have hUniformQ : TendstoUniformlyOn
      (fun n => (wQ n).toH1Function.toFun) Vrep atTop
        (closure (Q : Set (SpatialCoordinates d))) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hPε := (Metric.tendstoUniformlyOn_iff.mp hUniformP) ε hε
    filter_upwards [hPε] with n hn x hxQ
    by_cases hxP : x ∈ (P : Set (SpatialCoordinates d))
    · have hxPc : x ∈ closure (P : Set (SpatialCoordinates d)) := subset_closure hxP
      have hEqExt := (hwQ n).2.1 hxPc
      have hEqLimit := hVQeqVp hxPc
      have hEqVrep := hVrepVQ x hxQ
      rw [hEqExt, hEqVrep, hEqLimit]
      exact hn x hxPc
    · have hextzero := (hwQ n).2.2.1 x hxP
      have hrepzero : Vrep x = 0 := by
        rw [hVrepVQ x hxQ]
        exact hVQzero x hxP
      rw [hextzero, hrepzero]
      simpa only [dist_self] using hε
  have hlimQ : TendstoUniformly
      (fun n (x : closure (Q : Set (SpatialCoordinates d))) =>
        (wQ n).toH1Function.toFun x.val)
      (fun x => Vrep x.val) atTop := by
    rw [Metric.tendstoUniformly_iff]
    rw [Metric.tendstoUniformlyOn_iff] at hUniformQ
    intro ε hε
    filter_upwards [hUniformQ ε hε] with n hn x
    exact hn x x.property
  have hL2 : Tendsto (fun n => (wS n).val.1) atTop (𝓝 vQ) :=
    cube_tendsto_of_uniformly_on z hr
      (fun n => (wQ n).toH1Function.toFun)
      (fun n => (wS n).val.1)
      (fun n => sobolevDataOfH1_fst_coeFn (wQ n).toH1Function)
      Vrep vQ hvQrep hlimQ
  obtain ⟨nu, sigma, hsigma, hnufin, hnusupp, hConvMu⟩ :=
    aux_prop_boundary_weak_cluster (closure (Q : Set (SpatialCoordinates d)))
      (centeredCube_isBounded z hr).isCompact_closure muN (∑ k, Ecell k) hSupport hMass
  obtain ⟨hv, hdominate⟩ :=
    goodext_controlled_cluster_bank hd z r hr S hS a A c hc hell hrep
      t alpha ha hcell GN G hGN hConv E hE hcont Gamma
      rho hrho vQ wS (∑ k, Ecell k) nu sigma hnufin hnusupp hsigma hL2 hBound
      (by
        intro phi hphi
        simpa only [muN] using hConvMu phi hphi)
  refine ⟨vQ, Vrep, hv, hVrepcont, hvQrep, ?_⟩
  intro k
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxcell := frontier_subset_closure hx
    have hxPc : x ∈ closure (P : Set (SpatialCoordinates d)) :=
      closure_mono (oddGridCell_subset z0 hr0 (triadicHalf J) k) hxcell
    have hxQc : x ∈ closure (Q : Set (SpatialCoordinates d)) := hPcQ hxPc
    by_cases hxP : x ∈ (P : Set (SpatialCoordinates d))
    · calc
        Vrep x = VQ x := hVrepVQ x hxQc
        _ = Vp x := hVQeqVp hxPc
        _ = g x := hTraceP k x hx
    · have hxPfront : x ∈ frontier (P : Set (SpatialCoordinates d)) := by
        rw [frontier_eq_closure_inter_closure]
        refine ⟨hxPc, ?_⟩
        rw [closure_compl, P.isOpen.interior_eq]
        exact hxP
      calc
        Vrep x = VQ x := hVrepVQ x hxQc
        _ = 0 := hVQzero x hxP
        _ = g x := (hg0 x hxPfront).symm
  · have hnuCell :
        nu (oddGridCell z0 r0 hr0 (triadicHalf J) k : Set (SpatialCoordinates d)) ≤
          ENNReal.ofReal (Ecell k) := aux_prop_boundary_open_le
      (closure (Q : Set (SpatialCoordinates d))) (fun n => muN (sigma n)) nu
      (fun n => (hMass (sigma n)).trans_lt ENNReal.ofReal_lt_top) hnufin hConvMu
      (oddGridCell z0 r0 hr0 (triadicHalf J) k)
      (oddGridCell z0 r0 hr0 (triadicHalf J) k).isOpen
      (ENNReal.ofReal (Ecell k)) (fun n => hLocal (sigma n) k)
    have hle := (hdominate _ (oddGridCell z0 r0 hr0 (triadicHalf J) k).isOpen.measurableSet).trans hnuCell
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq
      (ENNReal.toReal_ofReal (hEc k))

end Paper
