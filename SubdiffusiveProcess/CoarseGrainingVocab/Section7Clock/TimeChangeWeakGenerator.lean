import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumInterface
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastScalarBridge
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.MassiveWeakSolutionAlgebra




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open Filter MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open MarkovProcess MarkovProcess.Semigroup
open scoped ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-! ### Local ellipticity bounds for a continuous positive coefficient -/

/-- The repository's bounded-domain predicate gives Mathlib boundedness. -/
theorem isBounded_of_isBoundedDomain {U : Set (Vec d)} (hU : IsBoundedDomain U) :
    Bornology.IsBounded U := by
  obtain ⟨R, hR, hb⟩ := hU
  rw [Metric.isBounded_iff_subset_closedBall (0 : Vec d)]
  refine ⟨R, fun x hx ↦ ?_⟩
  simp only [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg hR.le).2 fun i ↦ ?_
  simpa only [Real.norm_eq_abs] using hb x hx i

/-- Every centred cube is bounded. -/
theorem isBounded_cube (d : ℕ) (m : ℤ) : Bornology.IsBounded (cube d m) :=
  isBounded_of_isBoundedDomain
    (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d m).isBoundedDomain

/-- A continuous positive coefficient is bounded above and below by positive
constants on every bounded set. -/
theorem exists_bounds_of_isBounded {a : Vec d → ℝ}
    (hcont : Continuous a) (hpos : ∀ x, 0 < a x) {W : Set (Vec d)}
    (hW : Bornology.IsBounded W) :
    ∃ lam Lam : ℝ, 0 < lam ∧ ∀ x ∈ W, lam ≤ a x ∧ a x ≤ Lam := by
  classical
  obtain ⟨r, hr⟩ := hW.subset_closedBall (0 : Vec d)
  set s : ℝ := max r 0 with hs
  have hsr : (0 : ℝ) ≤ s := le_max_right _ _
  have hsub : W ⊆ Metric.closedBall (0 : Vec d) s :=
    hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hK : IsCompact (Metric.closedBall (0 : Vec d) s) := isCompact_closedBall _ _
  have hne : (Metric.closedBall (0 : Vec d) s).Nonempty := ⟨0, Metric.mem_closedBall_self hsr⟩
  obtain ⟨xmin, _, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  obtain ⟨xmax, _, hmax⟩ := hK.exists_isMaxOn hne hcont.continuousOn
  exact ⟨a xmin, a xmax, hpos xmin, fun x hx ↦ ⟨hmin (hsub hx), hmax (hsub hx)⟩⟩

/-- The chosen cube bounds of a continuous positive coefficient. -/
theorem exists_cube_bounds {a : Vec d → ℝ}
    (hcont : Continuous a) (hpos : ∀ x, 0 < a x) (n : ℕ) :
    ∃ p : ℝ × ℝ, 0 < p.1 ∧ ∀ x ∈ cube d (n : ℤ), p.1 ≤ a x ∧ a x ≤ p.2 := by
  obtain ⟨lam, Lam, hlam, hb⟩ := exists_bounds_of_isBounded hcont hpos (isBounded_cube d (n : ℤ))
  exact ⟨(lam, Lam), hlam, hb⟩

/-- **The reversible cube bounds of a continuous positive coefficient.**  This
is the ellipticity package that the whole-space uniqueness theorem of
`ResolventDatumUniqueness.lean` consumes, for the pair `(a, a)`. -/
def reversibleCubeBounds {a : Vec d → ℝ}
    (hcont : Continuous a) (hpos : ∀ x, 0 < a x) : MassiveCubeBounds a a where
  lam n := (Classical.choose (exists_cube_bounds hcont hpos n)).1
  Lam n := (Classical.choose (exists_cube_bounds hcont hpos n)).2
  rhoMin n := (Classical.choose (exists_cube_bounds hcont hpos n)).1
  rhoMax n := (Classical.choose (exists_cube_bounds hcont hpos n)).2
  lam_pos n := (Classical.choose_spec (exists_cube_bounds hcont hpos n)).1
  rhoMin_pos n := (Classical.choose_spec (exists_cube_bounds hcont hpos n)).1
  ell n :=
    Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isOpen.measurableSet
      hcont.continuousOn (Classical.choose_spec (exists_cube_bounds hcont hpos n)).1
      (Classical.choose_spec (exists_cube_bounds hcont hpos n)).2
  coeff_lower n x hx := ((Classical.choose_spec (exists_cube_bounds hcont hpos n)).2 x hx).1
  rho_measurable n := hcont.aestronglyMeasurable.restrict
  rho_lower n x hx := ((Classical.choose_spec (exists_cube_bounds hcont hpos n)).2 x hx).1
  rho_bounded n := by
    filter_upwards [ae_restrict_mem
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isOpen.measurableSet]
      with x hx
    rw [abs_of_pos (hpos x)]
    exact ((Classical.choose_spec (exists_cube_bounds hcont hpos n)).2 x hx).2

/-! ### Changing the weight of a massive weak solution -/



theorem isMassiveWeakSolutionOn_reweight {W : Set (Vec d)} (hWmeas : MeasurableSet W)
    {c rho : Vec d → ℝ} {mu nu rhoMax : ℝ}
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    (hrhoNe : ∀ x ∈ W, rho x ≠ 0)
    {u : H1Function W} {f : Vec d → ℝ} (hf : MemL2On W f)
    (hu : IsMassiveWeakSolutionOn c (fun _ ↦ (1 : ℝ)) mu W u f) :
    IsMassiveWeakSolutionOn c rho nu W u
      (fun x ↦ nu * u.toFun x - (rho x)⁻¹ * (mu * u.toFun x - f x)) := by
  intro φ
  have hEq := hu φ
  have honeMeas : AEStronglyMeasurable (fun _ : Vec d ↦ (1 : ℝ)) (volume.restrict W) :=
    aestronglyMeasurable_const
  have honeBdd : ∀ᵐ x ∂(volume.restrict W), |(1 : ℝ)| ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun _ ↦ by norm_num
  have hI1 := integrableOn_mass_term hrhoMeas hrhoBdd u.memL2 φ.toH1Function.memL2
  have hI2 := integrableOn_mass_term honeMeas honeBdd u.memL2 φ.toH1Function.memL2
  have hI3 := integrableOn_mass_term honeMeas honeBdd hf φ.toH1Function.memL2
  have hpoint : (∫ x in W, rho x *
        (nu * u.toFun x - (rho x)⁻¹ * (mu * u.toFun x - f x)) *
        φ.toH1Function.toFun x ∂volume) =
      ∫ x in W, ((nu * (rho x * u.toFun x * φ.toH1Function.toFun x) -
        mu * ((1 : ℝ) * u.toFun x * φ.toH1Function.toFun x)) +
        (1 : ℝ) * f x * φ.toH1Function.toFun x) ∂volume := by
    refine setIntegral_congr_fun hWmeas fun x hx ↦ ?_
    have hne : rho x ≠ 0 := hrhoNe x hx
    field_simp
    ring
  have hRHS : (∫ x in W, rho x *
        (nu * u.toFun x - (rho x)⁻¹ * (mu * u.toFun x - f x)) *
        φ.toH1Function.toFun x ∂volume) =
      nu * (∫ x in W, rho x * u.toFun x * φ.toH1Function.toFun x ∂volume) -
        mu * (∫ x in W, (1 : ℝ) * u.toFun x * φ.toH1Function.toFun x ∂volume) +
        ∫ x in W, (1 : ℝ) * f x * φ.toH1Function.toFun x ∂volume := by
    have hIA : IntegrableOn (fun x ↦ nu * (rho x * u.toFun x * φ.toH1Function.toFun x) -
        mu * ((1 : ℝ) * u.toFun x * φ.toH1Function.toFun x)) W volume :=
      (hI1.const_mul nu).sub (hI2.const_mul mu)
    rw [hpoint, integral_add hIA hI3,
      integral_sub (hI1.const_mul nu) (hI2.const_mul mu), integral_const_mul,
      integral_const_mul]
  rw [hRHS]
  linarith [hEq]

/-- The weak equation only sees the forcing on `W`. -/
theorem isMassiveWeakSolutionOn_congr_forcing_on {c rho : Vec d → ℝ}
    {W : Set (Vec d)} (hWmeas : MeasurableSet W) {mu : ℝ} {u : H1Function W}
    {f g : Vec d → ℝ} (hfg : ∀ x ∈ W, f x = g x)
    (hu : IsMassiveWeakSolutionOn c rho mu W u f) :
    IsMassiveWeakSolutionOn c rho mu W u g := by
  intro φ
  have hEq := hu φ
  have hr : (∫ x in W, rho x * f x * φ.toH1Function.toFun x ∂volume) =
      ∫ x in W, rho x * g x * φ.toH1Function.toFun x ∂volume :=
    setIntegral_congr_fun hWmeas fun x hx ↦ by rw [hfg x hx]
  rw [← hr]
  exact hEq

/-! ### The identification of the two resolvents -/

/-- **The `(a,1)` resolvent is an `(a,a)` resolvent.**  If `h` is the `C₀`
function `mu g − a⁻¹ (mu g − f)` built from `g = R^{(a,1)}_mu f`, then
`R^{(a,a)}_mu h = g`.

This is the composition of the two weak elliptic characterizations that P-212
and P-219 identified as the missing link; it is available exactly when `h` is
again a `C₀` datum, and the caller must exhibit it. -/
theorem solution_reversible_eq_solution_divergence
    {a : Vec d → ℝ} (hcont : Continuous a) (hpos : ∀ x, 0 < a x)
    {DXd DYd : C0ResolventDatum (Vec d)}
    (hX : IsWeakEllipticResolvent a a DXd)
    (hY : IsWeakEllipticResolvent a (fun _ ↦ (1 : ℝ)) DYd)
    (mu : PositiveShift) (f h : C₀(Vec d, ℝ))
    (hh : ∀ x, h x = (mu : ℝ) * DYd.solution mu f x -
      (a x)⁻¹ * ((mu : ℝ) * DYd.solution mu f x - f x)) :
    DXd.solution mu h = DYd.solution mu f := by
  set B := reversibleCubeBounds hcont hpos with hB
  set g := DYd.solution mu f with hg
  set w := DXd.solution mu h with hw
  have hzero : ∀ x, w x - g x = 0 := by
    refine eq_zero_of_localMassiveWeakSolution_of_tendsto_cocompact B mu.property
      (u := fun x ↦ w x - g x) (w.continuous.sub g.continuous) ?_ ?_
    · simpa using (zero_at_infty w).sub (zero_at_infty g)
    · intro k
      set W := cube d (k : ℤ) with hWdef
      have hW := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
      have hWmeas : MeasurableSet W := hW.isOpen.measurableSet
      obtain ⟨v1, hv1, hs1⟩ := hX mu h W hW
      obtain ⟨v2, hv2, hs2⟩ := hY mu f W hW
      have hs2r : IsMassiveWeakSolutionOn a a (mu : ℝ) W v2
          (fun x ↦ (mu : ℝ) * v2.toFun x - (a x)⁻¹ * ((mu : ℝ) * v2.toFun x - f x)) :=
        isMassiveWeakSolutionOn_reweight hWmeas (B.rho_measurable k) (B.rho_bounded k)
          (fun x _ ↦ ne_of_gt (hpos x)) (memL2On_of_zeroAtInfty hW f) hs2
      have hs2' : IsMassiveWeakSolutionOn a a (mu : ℝ) W v2 (fun x ↦ h x) := by
        refine isMassiveWeakSolutionOn_congr_forcing_on hWmeas (fun x hx ↦ ?_) hs2r
        rw [hh x, hv2 x hx]
      have hsub := IsMassiveWeakSolutionOn.sub (B.ell k) (B.rho_measurable k) (B.rho_bounded k)
        (memL2On_of_zeroAtInfty hW h) (memL2On_of_zeroAtInfty hW h) hs1 hs2'
      refine ⟨v1 - v2, ?_, IsMassiveWeakSolutionOn.congr_forcing ?_ hsub⟩
      · filter_upwards [ae_restrict_mem hWmeas] with x hx
        simp only [H1Function.sub_toFun, hv1 x hx, hv2 x hx]
        rfl
      · funext x
        simp
  refine ZeroAtInftyContinuousMap.ext fun x ↦ ?_
  have := hzero x
  linarith [this]

/-! ### The `C₀` datum of the identification -/

/-- Multiplication of a `C₀` function by a bounded continuous function. -/
def c0MulBounded (b : Vec d → ℝ) (hb : Continuous b) {M : ℝ} (hM : ∀ x, |b x| ≤ M)
    (f : C₀(Vec d, ℝ)) : C₀(Vec d, ℝ) :=
  ⟨⟨fun x ↦ b x * f x, hb.mul f.continuous⟩, by
    refine squeeze_zero_norm (a := fun x ↦ M * ‖f x‖) (fun x ↦ ?_) ?_
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
    · have h := ((zero_at_infty f).norm).const_mul M
      simpa using h⟩

@[simp]
theorem c0MulBounded_apply (b : Vec d → ℝ) (hb : Continuous b) {M : ℝ} (hM : ∀ x, |b x| ≤ M)
    (f : C₀(Vec d, ℝ)) (x : Vec d) : c0MulBounded b hb hM f x = b x * f x := rfl

/-- The reciprocal of a coefficient bounded below by a positive constant is
bounded above. -/
theorem abs_inv_le_of_le {a : Vec d → ℝ} {eps : ℝ} (heps : 0 < eps)
    (hle : ∀ x, eps ≤ a x) (x : Vec d) : |(a x)⁻¹| ≤ eps⁻¹ := by
  have hax : 0 < a x := lt_of_lt_of_le heps (hle x)
  rw [abs_of_pos (inv_pos.mpr hax)]
  exact inv_anti₀ heps (hle x)

/-! ### The resolvent of the generated semigroup -/

/-- The resolvent of the `C₀` semigroup generated by a datum is the datum's own
solution operator. -/
theorem resolvent_c0Semigroup_eq_solution
    {D : C0ResolventDatum (Vec d)} (hdense : ∀ nu, DenseRange (D.operator nu))
    {P : SubMarkovKernelSemigroup (Vec d)} (hFeller : P.IsFellerKernelSemigroup)
    (hPeq : P = D.fellerKernelSemigroup hdense) (nu : PositiveShift) (k : C₀(Vec d, ℝ)) :
    hFeller.c0Semigroup.resolvent nu k = D.solution nu k := by
  refine ZeroAtInftyContinuousMap.ext fun x ↦ ?_
  rw [hFeller.resolvent_apply_apply nu k x, D.solution_eq_laplace hdense nu k x, hPeq]

/-! ### The generator identity -/

/-- **The identification, with the `C₀` obstruction as an explicit witness.**
The `(a,1)` resolvent `g = R^{(a,1)}_mu f` is the `(a,a)` resolvent of
`mu g − k` as soon as the reciprocal-weighted residual `k = a⁻¹ (mu g − f)` is
itself a `C₀` function.  That hypothesis *is* the statement `g ∈ D(L_X)`, and it
is the only thing separating the two weak elliptic characterizations. -/
theorem resolvent_eq_solution_divergence_of_c0
    {a : Vec d → ℝ} (hcont : Continuous a) (hpos : ∀ x, 0 < a x)
    {DXd DYd : C0ResolventDatum (Vec d)}
    (hdenseX : ∀ nu, DenseRange (DXd.operator nu))
    (hX : IsWeakEllipticResolvent a a DXd)
    (hY : IsWeakEllipticResolvent a (fun _ ↦ (1 : ℝ)) DYd)
    {P : SubMarkovKernelSemigroup (Vec d)} (hFeller : P.IsFellerKernelSemigroup)
    (hPeq : P = DXd.fellerKernelSemigroup hdenseX)
    (mu : PositiveShift) (f k : C₀(Vec d, ℝ))
    (hk : ∀ x, k x = (a x)⁻¹ * ((mu : ℝ) * DYd.solution mu f x - f x)) :
    hFeller.c0Semigroup.resolvent mu ((mu : ℝ) • DYd.solution mu f - k) =
      DYd.solution mu f := by
  rw [resolvent_c0Semigroup_eq_solution hdenseX hFeller hPeq]
  refine solution_reversible_eq_solution_divergence hcont hpos hX hY mu f _ fun x ↦ ?_
  simp [hk x]

/-- **The `(a,1)` resolvent lies in the domain of the `(a,a)` generator**, given
the `C₀` witness. -/
theorem mem_generatorDomain_solution_divergence_of_c0
    {a : Vec d → ℝ} (hcont : Continuous a) (hpos : ∀ x, 0 < a x)
    {DXd DYd : C0ResolventDatum (Vec d)}
    (hdenseX : ∀ nu, DenseRange (DXd.operator nu))
    (hX : IsWeakEllipticResolvent a a DXd)
    (hY : IsWeakEllipticResolvent a (fun _ ↦ (1 : ℝ)) DYd)
    {P : SubMarkovKernelSemigroup (Vec d)} (hFeller : P.IsFellerKernelSemigroup)
    (hPeq : P = DXd.fellerKernelSemigroup hdenseX)
    (mu : PositiveShift) (f k : C₀(Vec d, ℝ))
    (hk : ∀ x, k x = (a x)⁻¹ * ((mu : ℝ) * DYd.solution mu f x - f x)) :
    DYd.solution mu f ∈ hFeller.c0Semigroup.generatorDomain :=
  (hFeller.mem_generatorDomain_iff_exists_resolvent mu _).2
    ⟨_, resolvent_eq_solution_divergence_of_c0 hcont hpos hdenseX hX hY hFeller hPeq mu f k hk⟩



theorem generator_solution_divergence_of_c0
    {a : Vec d → ℝ} (hcont : Continuous a) (hpos : ∀ x, 0 < a x)
    {DXd DYd : C0ResolventDatum (Vec d)}
    (hdenseX : ∀ nu, DenseRange (DXd.operator nu))
    (hX : IsWeakEllipticResolvent a a DXd)
    (hY : IsWeakEllipticResolvent a (fun _ ↦ (1 : ℝ)) DYd)
    {P : SubMarkovKernelSemigroup (Vec d)} (hFeller : P.IsFellerKernelSemigroup)
    (hPeq : P = DXd.fellerKernelSemigroup hdenseX)
    (mu : PositiveShift) (f k : C₀(Vec d, ℝ))
    (hk : ∀ x, k x = (a x)⁻¹ * ((mu : ℝ) * DYd.solution mu f x - f x))
    (hmem : DYd.solution mu f ∈ hFeller.c0Semigroup.generatorDomain) (x : Vec d) :
    hFeller.c0Semigroup.generator ⟨DYd.solution mu f, hmem⟩ x =
      (a x)⁻¹ * ((mu : ℝ) * DYd.solution mu f x - f x) := by
  rw [hFeller.c0Semigroup.generator_eq_of_resolvent_eq mu hmem
    (resolvent_eq_solution_divergence_of_c0 hcont hpos hdenseX hX hY hFeller hPeq mu f k hk)]
  simp [hk x]

/-! ### The bounded-below instance of the witness -/

/-- For a coefficient bounded below the reciprocal-weighted residual is
automatically a `C₀` function. -/
theorem exists_c0_residual_of_lowerBound
    {a : Vec d → ℝ} (hcont : Continuous a) {eps : ℝ} (heps : 0 < eps)
    (hle : ∀ x, eps ≤ a x) (mu : PositiveShift) (f g : C₀(Vec d, ℝ)) :
    ∃ k : C₀(Vec d, ℝ), ∀ x, k x = (a x)⁻¹ * ((mu : ℝ) * g x - f x) :=
  ⟨c0MulBounded (fun x ↦ (a x)⁻¹)
      (hcont.inv₀ fun x ↦ ne_of_gt (lt_of_lt_of_le heps (hle x)))
      (abs_inv_le_of_le heps hle) ((mu : ℝ) • g - f), fun x ↦ by simp⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
