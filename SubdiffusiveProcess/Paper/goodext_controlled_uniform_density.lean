module

public import SubdiffusiveProcess.Paper.goodext_controlled_mesh_bank
public import SubdiffusiveProcess.Paper.prop_conc_mesh_compactness
public import SubdiffusiveProcess.Sobolev.UniformCubeLimit
public import SubdiffusiveProcess.DirichletForm.ResponseTraceLimit
public import SubdiffusiveProcess.DirichletForm.ThresholdApproximation
public import SubdiffusiveProcess.Sobolev.UniformSmoothSources
public import SubdiffusiveProcess.Sobolev.NativeBoundaryResponse

@[expose] public section

/-! Uniform density of continuous form-domain representatives for a controlled sequence.
Finite harmonic meshes and inverse convergence supply the domain membership;
normal contractions then give compactly supported approximations.
-/
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Uniformly compact harmonic meshes produce continuous domain approximations for the exact inverse-limit form. -/
theorem aux_goodext_controlled_uniform_density_smooth
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (c : ℕ → SpatialCoordinates d → ℝ) (hc : ∀ n, Continuous (c n))
    (hell : ∀ n, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), lam ≤ c n x ∧ c n x ≤ Lam)
    (hrep : ∀ n, (a n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] c n)
    (t alpha : ℝ) (ha : 0 < alpha)
    (hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr c t alpha)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hresponse : ∀ f : DomainL2 (centeredCube z r hr),
      Tendsto (fun n => inverseResponse S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL))
        atTop (𝓝 (inner ℝ f (G f))))
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (hcompact : HasCompactSupport phi)
    (hsupp : tsupport phi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ u ∈ E.domain, ∃ uc : SpatialCoordinates d → ℝ,
      ContinuousOn uc (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc ∧
      ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), |uc x - phi x| ≤ eps := by
  obtain ⟨J, w, Ebound, Hbound, hHbound, henergy, hcont, hholder, hclose⟩ :=
    goodext_controlled_mesh_bank hd z r hr c hc hell t alpha hcell phi hphi hcompact hsupp eps heps
  obtain ⟨tau, htau, g, hlim⟩ := prop_conc_mesh_compactness d hd z r hr J
    (fun n => (w n).toH1Function.toFun) hcont alpha ha Hbound hHbound
    (fun k n => (hholder k n).1) (fun k n => (hholder k n).2)
  obtain ⟨v, vc, hvc, hvrep, hvg⟩ := exists_cubeL2_of_continuous_closedCube z hr g
  let uN : ℕ → S.space := fun n =>
    ⟨sobolevDataOfH1 (w (tau n)).toH1Function, by
      rw [hS]
      exact sobolevDataOfH1_mem_killed (w (tau n))⟩
  have hvlim : Tendsto (fun n => (uN n).val.1) atTop (𝓝 v) :=
    cube_tendsto_of_uniformly_on z hr (fun n => (w (tau n)).toH1Function.toFun)
      (fun n => (uN n).val.1) (fun n => sobolevDataOfH1_fst_coeFn (w (tau n)).toH1Function)
      vc v hvrep (by
        have hfun : (fun x : closure (centeredCube z r hr : Set (SpatialCoordinates d)) => vc x.val) =
            (fun x => g x) := funext fun x => hvg x.val x.property
        rw [hfun]
        exact hlim)
  have he (n : ℕ) : responseForm S (a (tau n)) (uN n) (uN n) ≤ Ebound := by
    change sobolevCoefficientForm _ (sobolevDataOfH1 (w (tau n)).toH1Function)
      (sobolevDataOfH1 (w (tau n)).toH1Function) ≤ Ebound
    rw [← energy_eq_sobolevCoefficientForm _ _ (hrep (tau n))]
    exact henergy (tau n)
  have hv := form_bound_of_response_limits S (fun n => a (tau n)) G E hE
    (fun f => (hresponse f).comp htau.tendsto_atTop) uN v hvlim Ebound he
  refine ⟨v, hv.1, vc, hvc, hvrep, ?_⟩
  intro x hx
  rw [hvg x hx]
  exact le_of_tendsto' (((hlim.tendsto_at ⟨x, hx⟩).sub_const (phi x)).abs)
    (fun n => hclose (tau n) x hx)

/-- Smooth uniform domain approximation and normal contractions yield a uniformly dense compactly supported form core. -/
theorem goodext_controlled_uniform_density
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hNC : _root_.SubdiffusiveProcess.DirichletForm.HasNormalContractions E)
    (hsmooth : ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ eps : ℝ, 0 < eps → ∃ u ∈ E.toClosedForm.domain, ∃ uc : SpatialCoordinates d → ℝ,
        ContinuousOn uc (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc ∧
        ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), |uc x - phi x| ≤ eps)
    (phi : SpatialCoordinates d → ℝ) (hphi : Continuous phi) (hcompact : HasCompactSupport phi)
    (hsupp : tsupport phi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ w ∈ E.toClosedForm.domain, ∃ g : SpatialCoordinates d → ℝ,
      Continuous g ∧ HasCompactSupport g ∧
      tsupport g ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      ((w : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g) ∧
      ∀ x, |g x - phi x| < eps := by
  obtain ⟨psi, hpsi, hpsic, hpsis, hpsia⟩ := SmoothSources.exists_uniform_smooth_approximation
    phi hphi hcompact _ hsupp (eps / 4) (by positivity)
  obtain ⟨u, hu, uc, huc, hurep, huapp⟩ := hsmooth psi hpsi hpsic hpsis (eps / 8) (by positivity)
  obtain ⟨w, hw, g, hgc, hgs, hgQ, hrep, happ⟩ :=
    LimitFormCore.compact_approximation_of_continuous_domain z hr E hNC u hu uc huc hurep
      psi hpsic hpsis (eps / 4) (by positivity) (by
        intro x hx
        have heq : eps / 8 = (eps / 4) / 2 := by ring
        exact (huapp x hx).trans_eq heq)
  refine ⟨w, hw, g, hgc, hgs, hgQ, hrep, ?_⟩
  intro x
  have htri := abs_sub_le (g x) (psi x) (phi x)
  have h1 := happ x
  have h2 := hpsia x
  linarith only [htri, h1, h2, heps]

end SubdiffusiveProcess.Paper
