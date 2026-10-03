module

public import SubdiffusiveProcess.LocalSource.MaxPrinciple
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.LocalEnergy
public import SubdiffusiveProcess.Sobolev.WeakEquationRestrict
public import SubdiffusiveProcess.Lane2.CellDirichlet
public import SubdiffusiveProcess.Lane1.ChaosBasic

@[expose] public section

/-!
# Local sourced energy against the Dirichlet response

Dirichlet principle, weak maximum principle and zero extension give, for a weak solution `u` of
`-∇·(a∇u) = F` on `Ω` with `|u| ≤ K_s` and `|F| ≤ K_f`, and a cube `Q ⊂ Ω`:

`∫_Q a|∇u|² ≤ DirichletResponse_Q(a, u|_Q) + 2 K_f K_s |Q|`.

With `h` the harmonic minimizer of trace `v = u|_Q`: `E(v,v) = E(h,h) + E(v−h,v−h)` (orthogonality),
`E(v−h,v−h) = ∫_Q F(v−h)` (the zero extension of `v−h` is a killed test on `Ω`), and
`|h| ≤ K_s` by the weak maximum principle.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace SubdiffusiveProcess

variable {d : ℕ}

/-- The volume of a centred cube. -/
theorem localSource_volume_real_centeredCube (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) = r ^ d := by
  rw [centeredCube_coe_eq_ball, Measure.real, Real.volume_pi_ball z (by positivity),
    ENNReal.toReal_ofReal (by positivity), Fintype.card_fin]
  congr 1
  ring

/-- The local energy of a restricted graph element is the energy of its restriction. -/
theorem localSource_localGradientEnergy_eq {Ω Q : Opens (SpatialCoordinates d)} (hQ : Q ≤ Ω)
    (a : PositiveCoefficient Ω) (aq : PositiveCoefficient Q)
    (haq : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), aq.val x = a.val x)
    (u : SobolevData Ω) :
    localGradientEnergy a Q.isOpen.measurableSet (sobolevGradient u) =
      sobolevCoefficientForm aq (sobolevDataRestrict hQ u) (sobolevDataRestrict hQ u) := by
  rw [localGradientEnergy_eq_integral, sobolevCoefficientForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.restrict_restrict Q.isOpen.measurableSet, Set.inter_eq_left.mpr hQ]
  refine integral_congr_ae ?_
  filter_upwards [haq, domainLpRestrict_coeFn hQ (u.2 i)] with x hx1 hx2
  change a.val x * (sobolevGradient u i x) ^ 2 =
    aq.val x * (domainLpRestrict hQ (u.2 i) x * domainLpRestrict hQ (u.2 i) x)
  rw [hx1, hx2, sobolevGradient_apply]
  ring

/-- **Local source comparison**, for an arbitrary open subdomain `Q` that is a bounded convex
domain of finite volume. -/
theorem localSource_comparison {Ω Q : Opens (SpatialCoordinates d)} [NeZero d]
    (hQconv : Homogenization.IsOpenBoundedConvexDomain (Q : Set (SpatialCoordinates d)))
    (hvol : volume (Q : Set (SpatialCoordinates d)) < ⊤)
    (a : PositiveCoefficient Ω) (u : weakSobolevGraph Ω)
    (F : SpatialCoordinates d → ℝ) (Kf Ks : ℝ) (hKf : 0 ≤ Kf) (hKs : 0 ≤ Ks)
    (hFb : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (hweak : ∀ psi : killedSobolevGraph Ω,
      sobolevCoefficientForm a (u : SobolevData Ω) (psi : SobolevData Ω) =
        ∫ x in (Ω : Set (SpatialCoordinates d)), F x * (psi : SobolevData Ω).1 x)
    (U : SpatialCoordinates d → ℝ)
    (hu : ((u : SobolevData Ω).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω : Set (SpatialCoordinates d))] U)
    (hUb : ∀ x ∈ closure (Ω : Set (SpatialCoordinates d)), |U x| ≤ Ks)
    (hsub : Q ≤ Ω) (aq : PositiveCoefficient Q)
    (haq : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), aq.val x = a.val x)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph Q,
      ‖(v : SobolevData Q).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) v‖) :
    ∃ v : weakSobolevGraph Q,
      (((v : SobolevData Q).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
      localGradientEnergy a Q.isOpen.measurableSet (sobolevGradient (u : SobolevData Ω)) ≤
        dirichletResponse (killedResponseSpace hP) aq v +
          2 * Kf * Ks * volume.real (Q : Set (SpatialCoordinates d)) := by
  have hQmeas : MeasurableSet (Q : Set (SpatialCoordinates d)) := Q.isOpen.measurableSet
  let vW : weakSobolevGraph Q :=
    ⟨sobolevDataRestrict hsub u.val, sobolevDataRestrict_mem_weak hsub u.property⟩
  -- the restriction represents `U`, hence is bounded by `Ks`
  have hvU : ((vW : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Q : Set (SpatialCoordinates d))] U := by
    filter_upwards [domainLpRestrict_coeFn hsub u.val.1,
      ae_restrict_of_ae_restrict_of_subset hsub hu] with x h1 h2
    exact h1.trans h2
  have hvb : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      |(vW : SobolevData Q).1 x| ≤ Ks := by
    filter_upwards [hvU, ae_restrict_mem hQmeas] with x hx hxQ
    rw [hx]
    exact hUb x (subset_closure (hsub hxQ))
  refine ⟨vW, hvU, ?_⟩
  let S := killedResponseSpace hP
  let h := dirichletMinimizer S aq vW
  have hharm : ∀ psi : killedSobolevGraph Q,
      sobolevCoefficientForm aq h.val psi.val = 0 := fun psi =>
    dirichletMinimizer_euler S aq vW psi
  have hdiff : h.val - vW.val ∈ killedSobolevGraph Q := dirichletMinimizer_mem_affine S aq vW
  -- maximum principle
  have hhb : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), |h.val.1 x| ≤ Ks :=
    localSource_ae_abs_le hQconv aq h vW hharm hdiff hKs hvb
  -- the difference
  set x0 : SobolevData Q := vW.val - h.val with hx0
  have hx0mem : x0 ∈ killedSobolevGraph Q := by
    have := (killedSobolevGraph Q).neg_mem hdiff
    simpa [hx0] using this
  have hx0b : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), |x0.1 x| ≤ 2 * Ks := by
    filter_upwards [hvb, hhb, Lp.coeFn_sub (vW : SobolevData Q).1 h.val.1] with x h1 h2 h3
    have : x0.1 x = (vW : SobolevData Q).1 x - h.val.1 x := by
      simpa [hx0] using h3
    rw [this]
    calc |(vW : SobolevData Q).1 x - h.val.1 x| ≤ |(vW : SobolevData Q).1 x| + |h.val.1 x| :=
          abs_sub _ _
      _ ≤ 2 * Ks := by linarith
  -- energy identity
  have hgap := dirichletResponse_energy_gap S aq vW 0
  simp only [Submodule.coe_zero, add_zero] at hgap
  have hEh : sobolevCoefficientForm aq h.val x0 = 0 :=
    dirichletMinimizer_euler S aq vW ⟨x0, hx0mem⟩
  have hsource := weakEquation_restrict hsub a aq (haq.mono fun x hx => hx.symm) u.val F hweak
    ⟨x0, hx0mem⟩
  have hE0 : sobolevCoefficientForm aq x0 x0 =
      ∫ x in (Q : Set (SpatialCoordinates d)), F x * x0.1 x := by
    have e1 : sobolevCoefficientForm aq x0 x0 =
        sobolevCoefficientForm aq vW.val x0 - sobolevCoefficientForm aq h.val x0 := by
      have e := congrArg (fun T : SobolevData Q →L[ℝ] ℝ => T x0)
        (map_sub (sobolevCoefficientForm aq) vW.val h.val)
      simp only [ContinuousLinearMap.sub_apply] at e
      exact e
    rw [e1, hEh, sub_zero]
    exact hsource
  have hgap' : sobolevCoefficientForm aq vW.val vW.val =
      dirichletResponse S aq vW + sobolevCoefficientForm aq x0 x0 := by
    simpa [hx0] using hgap
  haveI : IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    isFiniteMeasure_restrict.mpr hvol.ne
  have hbound : sobolevCoefficientForm aq x0 x0 ≤
      2 * Kf * Ks * volume.real (Q : Set (SpatialCoordinates d)) := by
    rw [hE0]
    have hFQ : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), |F x| ≤ Kf :=
      ae_restrict_of_ae_restrict_of_subset hsub hFb
    have h1 : ‖∫ x in (Q : Set (SpatialCoordinates d)), F x * x0.1 x‖ ≤
        (Kf * (2 * Ks)) * (volume.restrict (Q : Set (SpatialCoordinates d))).real univ :=
      norm_integral_le_of_norm_le_const (by
        filter_upwards [hFQ, hx0b] with x h1 h2
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul h1 h2 (abs_nonneg _) hKf)
    have h2 : (volume.restrict (Q : Set (SpatialCoordinates d))).real univ =
        volume.real (Q : Set (SpatialCoordinates d)) := by
      rw [Measure.real, Measure.restrict_apply_univ]; rfl
    rw [h2] at h1
    calc _ ≤ ‖∫ x in (Q : Set (SpatialCoordinates d)), F x * x0.1 x‖ :=
          (le_abs_self _).trans (by rw [Real.norm_eq_abs])
      _ ≤ _ := h1
      _ = _ := by ring
  have hen := localSource_localGradientEnergy_eq hsub a aq haq (u : SobolevData Ω)
  rw [hen]
  change sobolevCoefficientForm aq vW.val vW.val ≤ _
  linarith [hgap', hbound]

end SubdiffusiveProcess
