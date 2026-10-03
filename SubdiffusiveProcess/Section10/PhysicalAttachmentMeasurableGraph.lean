module

public import SubdiffusiveProcess.Section10.PhysicalAttachmentMeasurableCore
@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess
open scoped ENNReal NNReal ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalAttachment
section aux_cubeRelation

open Filter MeasureTheory Topology Set
open scoped ZeroAtInfty ENNReal

open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

/-- The gradient vector field of an `L²` gradient family. -/
def pa_gradField {d : ℕ} {U : Set (Fin d → ℝ)}
    (G : Fin d → Lp ℝ 2 (volume.restrict U)) : (Fin d → ℝ) → (Fin d → ℝ) :=
  fun x i ↦ (G i : (Fin d → ℝ) → ℝ) x

/-- **The weak massive relation on one centred cube**, with the weak gradient parametrized by an
`L²` family: `G` is a weak gradient of `g` on the cube, and `(g, G)` satisfies the massive
equation `μ ρ g − ∇·(c ∇g) = ρ f` against every `H¹₀` test. -/
def pa_cubeRel (d k : ℕ) (mu : ℝ)
    (f : C₀(Fin d → ℝ, ℝ)) (c rho : (Fin d → ℝ) → ℝ) (g : C₀(Fin d → ℝ, ℝ))
    (G : Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) : Prop :=
  Homogenization.HasWeakGradientOn (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)) (fun x ↦ g x)
      (pa_gradField G) ∧
    ∀ φ : Homogenization.H10Function (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)),
      mu * ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
          rho x * g x * φ.toH1Function.toFun x ∂volume +
        ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
          Homogenization.vecDot
            (c x • pa_gradField G x)
            (φ.toH1Function.grad x) ∂volume =
      ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
        rho x * f x * φ.toH1Function.toFun x ∂volume

/-- The `H¹` function with value function `g` and gradient field `G`. -/
def pa_mkH1 {d k : ℕ} (g : C₀(Fin d → ℝ, ℝ))
    (G : Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))))
    (hG : Homogenization.HasWeakGradientOn (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))
      (fun x ↦ g x) (pa_gradField G)) :
    Homogenization.H1Function (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)) where
  toFun x := g x
  grad := pa_gradField G
  memL2 := memL2On_of_zeroAtInfty
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)) g
  gradMemL2 i := Lp.memLp (G i)
  hasWeakGradient := hG

/-- A relation witness is a weak solution of the massive equation. -/
theorem pa_cubeRel_solution {d k : ℕ} {mu : ℝ}
    {f : C₀(Fin d → ℝ, ℝ)} {c rho : (Fin d → ℝ) → ℝ} {g : C₀(Fin d → ℝ, ℝ)}
    {G : Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))}
    (h : pa_cubeRel d k mu f c rho g G) :
    IsMassiveWeakSolutionOn c rho mu (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))
      (pa_mkH1 g G h.1) (fun x ↦ f x) :=
  h.2

/-- **Existence of a relation witness** from a weak elliptic resolvent datum. -/
theorem pa_cubeRel_of_weak {d : ℕ}
    {c rho : (Fin d → ℝ) → ℝ} {D : C0ResolventDatum (Fin d → ℝ)}
    (hD : IsWeakEllipticResolvent c rho D) (mu : MarkovProcess.Semigroup.PositiveShift)
    (f : C₀(Fin d → ℝ, ℝ)) (k : ℕ) :
    ∃ G, pa_cubeRel d k (mu : ℝ) f c rho
      (D.solution mu f) G := by
  have hW := SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
  have hUm : MeasurableSet (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)) := hW.isOpen.measurableSet
  obtain ⟨u, hu, husol⟩ := hD mu f _ hW
  let G : Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))) :=
    fun i ↦ (u.gradMemL2 i).toLp _
  have hGae : ∀ i, (G i : (Fin d → ℝ) → ℝ) =ᵐ[volume.restrict
      (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))] fun x ↦ u.grad x i :=
    fun i ↦ MemLp.coeFn_toLp _
  have hGall : ∀ᵐ x ∂(volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))),
      pa_gradField G x = u.grad x := by
    filter_upwards [ae_all_iff.2 hGae] with x hx
    funext i
    exact hx i
  refine ⟨G, ?_, ?_⟩
  · intro i φ hφ hφc hφs
    have h1 := u.hasWeakGradient i φ hφ hφc hφs
    have hl : ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
        D.solution mu f x * (fderiv ℝ φ x) (Homogenization.basisVec i) ∂volume =
        ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
          u.toFun x * (fderiv ℝ φ x) (Homogenization.basisVec i) ∂volume := by
      refine setIntegral_congr_fun hUm fun x hx ↦ ?_
      simp only [hu x hx]
    have hr : ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
        pa_gradField G x i * φ x ∂volume =
        ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ), u.grad x i * φ x ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards [hGall] with x hx
      rw [hx]
    simp only at h1 ⊢
    rw [hl, hr]
    exact h1
  · intro φ
    have h1 := husol φ
    have hl : ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
        rho x * D.solution mu f x * φ.toH1Function.toFun x ∂volume =
        ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
          rho x * u.toFun x * φ.toH1Function.toFun x ∂volume := by
      refine setIntegral_congr_fun hUm fun x hx ↦ ?_
      simp only [hu x hx]
    have hr : ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
        Homogenization.vecDot
          (c x • pa_gradField G x)
          (φ.toH1Function.grad x) ∂volume =
        ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
          Homogenization.vecDot (c x • u.grad x) (φ.toH1Function.grad x) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards [hGall] with x hx
      rw [hx]
    rw [hl, hr]
    exact h1

/-- The origin lies in every centred cube. -/
theorem pa_zero_mem_cube (d n : ℕ) :
    (0 : Fin d → ℝ) ∈ SubdiffusiveProcess.CoarseGrainingVocab.cube d (n : ℤ) := by
  rw [SubdiffusiveProcess.CoarseGrainingVocab.cube, Homogenization.mem_openCubeSet_originCube_iff]
  intro i
  have hhalf : (0 : ℝ) < (1 / 2) * (3 : ℝ) ^ (n : ℤ) := by positivity
  constructor
  · simp only [Pi.zero_apply]
    linarith
  · simp only [Pi.zero_apply]
    linarith

/-- A continuous function attains its minimum and maximum on the closure of a centred cube. -/
theorem pa_cube_extrema {d : ℕ}
    {c : (Fin d → ℝ) → ℝ} (hc : Continuous c) (n : ℕ) :
    (∃ x ∈ closure (SubdiffusiveProcess.CoarseGrainingVocab.cube d (n : ℤ)),
      IsMinOn c (closure (SubdiffusiveProcess.CoarseGrainingVocab.cube d (n : ℤ))) x) ∧
    (∃ x ∈ closure (SubdiffusiveProcess.CoarseGrainingVocab.cube d (n : ℤ)),
      IsMaxOn c (closure (SubdiffusiveProcess.CoarseGrainingVocab.cube d (n : ℤ))) x) := by
  have hK : IsCompact (closure (SubdiffusiveProcess.CoarseGrainingVocab.cube d (n : ℤ))) :=
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)
      ).isBoundedDomain.isBounded.isCompact_closure
  have hne : (closure (SubdiffusiveProcess.CoarseGrainingVocab.cube d (n : ℤ))).Nonempty :=
    ⟨0, subset_closure (pa_zero_mem_cube d n)⟩
  exact ⟨hK.exists_isMinOn hne hc.continuousOn, hK.exists_isMaxOn hne hc.continuousOn⟩

/-- Continuous positive coefficients have the local cube bounds used by whole-space uniqueness. -/
theorem pa_cube_bounds
    {d : ℕ} {c rho : (Fin d → ℝ) → ℝ}
    (hc : Continuous c) (hcpos : ∀ x, 0 < c x)
    (hrho : Continuous rho) (hrhopos : ∀ x, 0 < rho x) :
    Nonempty (MassiveCubeBounds c rho) := by
  choose xmin hxmin hmin using fun n ↦
    (pa_cube_extrema hc n).1
  choose xmax hxmax hmax using fun n ↦
    (pa_cube_extrema hc n).2
  choose rmin hrmin hrmin' using fun n ↦
    (pa_cube_extrema hrho n).1
  choose rmax hrmax hrmax' using fun n ↦
    (pa_cube_extrema hrho n).2
  let B : MassiveCubeBounds c rho :=
    { lam := fun n ↦ c (xmin n), Lam := fun n ↦ c (xmax n),
      rhoMin := fun n ↦ rho (rmin n), rhoMax := fun n ↦ rho (rmax n),
      lam_pos := fun n ↦ hcpos (xmin n),
      rhoMin_pos := fun n ↦ hrhopos (rmin n), ell := by
        intro n
        apply SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
            (n : ℤ)).isOpen.measurableSet
          hc.continuousOn (hcpos (xmin n))
        intro x hx
        exact ⟨hmin n (subset_closure hx), hmax n (subset_closure hx)⟩,
      coeff_lower := by
        intro n x hx
        exact hmin n (subset_closure hx),
      rho_measurable := by
        intro n
        exact hrho.aestronglyMeasurable,
      rho_lower := by
        intro n x hx
        exact hrmin' n (subset_closure hx),
      rho_bounded := by
        intro n
        filter_upwards [ae_restrict_mem
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
            (n : ℤ)).isOpen.measurableSet] with x hx
        rw [abs_of_pos (hrhopos x)]
        exact hrmax' n (subset_closure hx) }
  exact ⟨B⟩

/-- **Uniqueness of the relation section** under local cube bounds: two `C₀` functions carrying
relation witnesses on every centred cube coincide. -/
theorem pa_cubeRel_unique {d : ℕ} {mu : ℝ}
    (hmu : 0 < mu) {f : C₀(Fin d → ℝ, ℝ)} {c rho : (Fin d → ℝ) → ℝ}
    (B : MassiveCubeBounds c rho) {g g' : C₀(Fin d → ℝ, ℝ)}
    (h : ∀ k, ∃ G, pa_cubeRel d k mu f c rho g G)
    (h' : ∀ k, ∃ G,
      pa_cubeRel d k mu f c rho g' G) :
    g = g' := by
  have hdecay : Tendsto (fun x ↦ g x - g' x) (cocompact (Fin d → ℝ)) (𝓝 0) := by
    have := zero_at_infty (g - g')
    simpa using! this
  have hzero := eq_zero_of_localMassiveWeakSolution_of_tendsto_cocompact B hmu
    (u := fun x ↦ g x - g' x) (g.continuous.sub g'.continuous) hdecay (fun k ↦ by
      have hW := SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube
        d (k : ℤ)
      obtain ⟨G, hG⟩ := h k
      obtain ⟨G', hG'⟩ := h' k
      have hs := IsMassiveWeakSolutionOn.sub (B.ell k) (B.rho_measurable k) (B.rho_bounded k)
        (memL2On_of_zeroAtInfty hW f) (memL2On_of_zeroAtInfty hW f)
        (pa_cubeRel_solution hG)
        (pa_cubeRel_solution hG')
      refine ⟨pa_mkH1 g G hG.1 -
          pa_mkH1 g' G' hG'.1,
        Eventually.of_forall fun x ↦ ?_, IsMassiveWeakSolutionOn.congr_forcing ?_ hs⟩
      · simp [Homogenization.H1Function.sub_toFun, pa_mkH1]
      · funext x
        simp)
  ext x
  exact sub_eq_zero.1 (hzero x)

end aux_cubeRelation

section aux_closedness

open Filter MeasureTheory Topology Set
open scoped ZeroAtInfty ENNReal

open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

/-- The coefficient profile `y ↦ a e^{y - z}`. -/
def pa_coefFun (a z : ℝ) : C(ℝ, ℝ) :=
  ⟨fun y ↦ a * Real.exp (y - z), by fun_prop⟩

/-- The speed profile `y ↦ e^{y - z}`. -/
def pa_rhoFun (z : ℝ) : C(ℝ, ℝ) :=
  ⟨fun y ↦ Real.exp (y - z), by fun_prop⟩

/-- A continuous function is integrable against an `L²` function on a bounded set. -/
theorem pa_integrable_grad_term
    {d : ℕ} {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    {ψ : (Fin d → ℝ) → ℝ} (hψ : MemLp ψ 2 (volume.restrict U)) (c : C(Fin d → ℝ, ℝ))
    (G : Lp ℝ 2 (volume.restrict U)) :
    Integrable (fun x ↦ c x * (G : (Fin d → ℝ) → ℝ) x * ψ x) (volume.restrict U) := by
  refine (L2.integrable_inner (𝕜 := ℝ) G
    (pa_mulLp hU hUb hψ c)).congr ?_
  filter_upwards [pa_mulLp_ae hU hUb hψ c]
    with x hx
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The gradient term of the weak equation splits into coordinate `L²` pairings. -/
theorem pa_integral_vecDot
    {d : ℕ} {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    {Ψ : (Fin d → ℝ) → (Fin d → ℝ)} (hΨ : ∀ i, MemLp (fun x ↦ Ψ x i) 2 (volume.restrict U))
    (c : C(Fin d → ℝ, ℝ)) (G : Fin d → Lp ℝ 2 (volume.restrict U)) :
    ∫ x in U, Homogenization.vecDot
        (c x • pa_gradField G x) (Ψ x) ∂volume =
      ∑ i, ∫ x in U, c x * (G i : (Fin d → ℝ) → ℝ) x * Ψ x i := by
  rw [← integral_finset_sum _ fun i _ ↦
    pa_integrable_grad_term hU hUb (hΨ i) c (G i)]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [Homogenization.vecDot, pa_gradField,
    Pi.smul_apply, smul_eq_mul]

/-- **The relation set on one cube is closed** in the Polish product of potentials, `C₀`
values and `L²` gradient families. -/
theorem pa_isClosed_cubeRel
    (d k : ℕ) (a z mu : ℝ) (f : C₀(Fin d → ℝ, ℝ)) :
    IsClosed {q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
        (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) |
      pa_cubeRel d k mu f
        ((pa_coefFun a z).comp q.1)
        ((pa_rhoFun z).comp q.1) q.2.1 q.2.2} := by
  have hW := SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
  have hU : MeasurableSet (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)) := hW.isOpen.measurableSet
  have hUb : Bornology.IsBounded (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)) :=
    hW.isBoundedDomain.isBounded
  haveI : IsFiniteMeasure (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))) :=
    hW.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hcoef : Continuous fun q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
      (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) ↦
      (pa_coefFun a z).comp q.1 :=
    (ContinuousMap.continuous_postcomp _).comp continuous_fst
  have hrho : Continuous fun q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
      (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) ↦
      (pa_rhoFun z).comp q.1 :=
    (ContinuousMap.continuous_postcomp _).comp continuous_fst
  -- weak-gradient conditions
  have hWG : IsClosed {q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
      (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) |
      Homogenization.HasWeakGradientOn (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))
        (fun x ↦ q.2.1 x) (pa_gradField q.2.2)} := by
    simp only [Homogenization.HasWeakGradientOn, Homogenization.HasWeakPartialDerivOn,
      Set.setOf_forall]
    refine isClosed_iInter fun i ↦ isClosed_iInter fun φ ↦ isClosed_iInter fun hφ ↦
      isClosed_iInter fun hφc ↦ isClosed_iInter fun _ ↦ isClosed_eq ?_ ?_
    · have hψ : IntegrableOn (fun x ↦ (fderiv ℝ φ x) (Homogenization.basisVec i))
          (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)) := by
        have hcont : Continuous fun x ↦ (fderiv ℝ φ x) (Homogenization.basisVec i) :=
          (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
        have hcs : HasCompactSupport fun x ↦ (fderiv ℝ φ x) (Homogenization.basisVec i) :=
          hφc.fderiv_apply (𝕜 := ℝ) _
        exact (hcont.integrable_of_hasCompactSupport hcs).integrableOn
      have hg : Continuous fun q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
          (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) ↦
          ((1 : C(Fin d → ℝ, ℝ)), q.2.1) :=
        continuous_const.prodMk (continuous_fst.comp continuous_snd)
      have h := (pa_continuous_mass
        hU hUb hψ).comp hg
      refine h.congr fun q ↦ ?_
      simp
    · have hψ : MemLp φ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ))) :=
        (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict _
      have hGi : Continuous fun q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
          (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) ↦
          ((1 : C(Fin d → ℝ, ℝ)), q.2.2 i) :=
        continuous_const.prodMk ((continuous_apply i).comp (continuous_snd.comp continuous_snd))
      have h := (pa_continuous_grad
        hU hUb hψ).comp hGi
      refine (h.neg).congr fun q ↦ ?_
      simp [pa_gradField]
  -- equation conditions
  have hEQ : IsClosed {q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
      (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) |
      ∀ φ : Homogenization.H10Function (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)),
        mu * ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
            (pa_rhoFun z).comp q.1 x * q.2.1 x *
              φ.toH1Function.toFun x ∂volume +
          ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
            Homogenization.vecDot
              ((pa_coefFun a z).comp q.1 x •
                pa_gradField q.2.2 x)
              (φ.toH1Function.grad x) ∂volume =
        ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
          (pa_rhoFun z).comp q.1 x * f x *
            φ.toH1Function.toFun x ∂volume} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun φ ↦ isClosed_eq ?_ ?_
    · have hψ : IntegrableOn φ.toH1Function.toFun (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)) :=
        φ.toH1Function.memL2.integrable one_le_two
      have hmass := (pa_continuous_mass
        hU hUb hψ).comp (hrho.prodMk (continuous_fst.comp continuous_snd))
      have hgrad : Continuous fun q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
          (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) ↦
          ∑ i, ∫ x in SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ),
            (pa_coefFun a z).comp q.1 x *
              (q.2.2 i : (Fin d → ℝ) → ℝ) x * φ.toH1Function.grad x i := by
        refine continuous_finset_sum _ fun i _ ↦ ?_
        have hGi : Continuous fun q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
            (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) ↦
            ((pa_coefFun a z).comp q.1, q.2.2 i) :=
          hcoef.prodMk ((continuous_apply i).comp (continuous_snd.comp continuous_snd))
        exact (pa_continuous_grad hU hUb
          (φ.toH1Function.gradMemL2 i)).comp hGi
      refine (((continuous_const (y := mu)).mul hmass).add hgrad).congr fun q ↦ ?_
      simp only [Function.comp_apply]
      rw [pa_integral_vecDot hU hUb
        φ.toH1Function.gradMemL2]
      simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
    · have hψ : IntegrableOn φ.toH1Function.toFun (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)) :=
        φ.toH1Function.memL2.integrable one_le_two
      exact (pa_continuous_mass
        hU hUb hψ).comp (hrho.prodMk continuous_const)
  exact hWG.inter hEQ

end aux_closedness

section aux_graph

open Filter MeasureTheory Topology Set
open scoped ZeroAtInfty ENNReal

open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

/-- The graph of the whole-space weak massive solution operator over potentials: `(p, g)` lies
in it when `g ∈ C₀` solves `μ ρ_p g − ∇·(c_p ∇g) = ρ_p f` weakly on every centred cube, with
`c_p = a e^{p - z}` and `ρ_p = e^{p - z}`. -/
def pa_graph (d : ℕ) (a z mu : ℝ)
    (f : C₀(Fin d → ℝ, ℝ)) : Set (C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ)) :=
  {pg | ∀ k : ℕ, ∃ G, pa_cubeRel d k mu f
    ((pa_coefFun a z).comp pg.1)
    ((pa_rhoFun z).comp pg.1) pg.2 G}

theorem pa_potential_polish (d : ℕ) :
    PolishSpace C(Fin d → ℝ, ℝ) := by
  letI : TopologicalSpace.IsCompletelyMetrizableSpace C(Fin d → ℝ, ℝ) :=
    TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
      (X := C(Fin d → ℝ, ℝ))
  infer_instance

/-- **The solution graph is analytic**: it is a countable intersection of projections of closed
subsets of Polish spaces. -/
theorem pa_analytic_graph (d : ℕ) (a z mu : ℝ)
    (f : C₀(Fin d → ℝ, ℝ)) :
    AnalyticSet (pa_graph d a z mu f) := by
  haveI := pa_potential_polish d
  haveI := pa_c0_polish d
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have heq : pa_graph d a z mu f =
      ⋂ k : ℕ, (fun q : C(Fin d → ℝ, ℝ) × C₀(Fin d → ℝ, ℝ) ×
          (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) ↦
          (q.1, q.2.1)) ''
        {q | pa_cubeRel d k mu f
          ((pa_coefFun a z).comp q.1)
          ((pa_rhoFun z).comp q.1)
          q.2.1 q.2.2} := by
    ext ⟨p, g⟩
    simp only [pa_graph, mem_setOf_eq,
      mem_iInter, mem_image, Prod.exists, Prod.mk.injEq]
    constructor
    · intro h k
      obtain ⟨G, hG⟩ := h k
      exact ⟨p, g, G, hG, rfl, rfl⟩
    · intro h k
      obtain ⟨p', g', G, hG, rfl, rfl⟩ := h k
      exact ⟨G, hG⟩
  rw [heq]
  refine AnalyticSet.iInter fun k ↦ ?_
  haveI hL2 : SecondCountableTopology
      (Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) := inferInstance
  haveI : SecondCountableTopology
      (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) :=
    inferInstance
  haveI : PolishSpace
      (Fin d → Lp ℝ 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.cube d (k : ℤ)))) :=
    inferInstance
  exact (pa_isClosed_cubeRel d k a z mu f
    ).analyticSet.image_of_continuous (continuous_fst.prodMk (continuous_fst.comp continuous_snd))

/-- The solution graph is single-valued over every potential. -/
theorem pa_graph_unique {d : ℕ} {a z mu : ℝ}
    (ha : 0 < a) (hmu : 0 < mu) (f : C₀(Fin d → ℝ, ℝ)) (p : C(Fin d → ℝ, ℝ))
    (g g' : C₀(Fin d → ℝ, ℝ))
    (hg : (p, g) ∈ pa_graph d a z mu f)
    (hg' : (p, g') ∈ pa_graph d a z mu f) :
    g = g' := by
  obtain ⟨B⟩ := pa_cube_bounds
    (c := (pa_coefFun a z).comp p)
    (rho := (pa_rhoFun z).comp p)
    (ContinuousMap.continuous _) (fun x ↦ mul_pos ha (Real.exp_pos _))
    (ContinuousMap.continuous _) (fun x ↦ Real.exp_pos _)
  exact pa_cubeRel_unique hmu B hg hg'

/-- **Measurability of the canonical resolvent section.** A map carrying every parameter of a
set `G` to the (unique) `C₀` weak solution over a measurable potential is measurable on `G`. -/
theorem pa_measurable_section {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C(Fin d → ℝ, ℝ)] [BorelSpace C(Fin d → ℝ, ℝ)]
    {a z mu : ℝ} (ha : 0 < a) (hmu : 0 < mu) (f : C₀(Fin d → ℝ, ℝ))
    (Pot : Ω → C(Fin d → ℝ, ℝ)) (hPot : Measurable Pot) (G : Set Ω)
    (s : Ω → C₀(Fin d → ℝ, ℝ))
    (hs : ∀ ω ∈ G, (Pot ω, s ω) ∈ pa_graph d a z mu f) :
    @Measurable G C₀(Fin d → ℝ, ℝ) _ (borel _) fun ω ↦ s ω := by
  letI : MeasurableSpace C₀(Fin d → ℝ, ℝ) := borel _
  haveI : BorelSpace C₀(Fin d → ℝ, ℝ) := ⟨rfl⟩
  haveI := pa_potential_polish d
  haveI := pa_c0_polish d
  exact pa_measurable_of_analytic
    (pa_graph d a z mu f)
    (pa_analytic_graph d a z mu f)
    (pa_graph_unique ha hmu f)
    Pot hPot G s hs

end aux_graph
end SubdiffusiveProcess.Section10.PhysicalAttachment
