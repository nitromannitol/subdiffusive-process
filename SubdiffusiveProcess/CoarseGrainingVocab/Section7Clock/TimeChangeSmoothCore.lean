module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeDenseResidual
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumSmoothRange

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.Frozen.Section7
open MarkovProcess.Semigroup
open scoped ENNReal NNReal ZeroAtInfty Topology CompactlySupported

noncomputable section

variable {d : ℕ}

/-! ### The cube bounds of the divergence-form pair `(a, 1)` -/

/-- **The divergence-form cube bounds of a continuous positive coefficient.**
The companion of `reversibleCubeBounds` for the pair `(a, 1)`, whose generator
is `∇·(a∇)`; the weight is the constant `1`, so its bounds are trivial. -/
def divergenceCubeBounds {a : Vec d → ℝ} (hcont : Continuous a) (hpos : ∀ x, 0 < a x) :
    MassiveCubeBounds a (fun _ ↦ (1 : ℝ)) where
  lam n := (Classical.choose (exists_cube_bounds hcont hpos n)).1
  Lam n := (Classical.choose (exists_cube_bounds hcont hpos n)).2
  rhoMin _ := 1
  rhoMax _ := 1
  lam_pos n := (Classical.choose_spec (exists_cube_bounds hcont hpos n)).1
  rhoMin_pos _ := one_pos
  ell n :=
    Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isOpen.measurableSet
      hcont.continuousOn (Classical.choose_spec (exists_cube_bounds hcont hpos n)).1
      (Classical.choose_spec (exists_cube_bounds hcont hpos n)).2
  coeff_lower n x hx := ((Classical.choose_spec (exists_cube_bounds hcont hpos n)).2 x hx).1
  rho_measurable _ := aestronglyMeasurable_const
  rho_lower _ _ _ := le_rfl
  rho_bounded _ := Filter.Eventually.of_forall fun _ ↦ by norm_num

/-! ### The classical forcing of a smooth compactly supported function -/

/-- **A smooth compactly supported function is the `(a,1)` resolvent of its
classical forcing.**  If `F = mu w − ∇·(a∇w)` as a `C₀` datum, then
`R^{(a,1)}_mu F = w`.

This is the `C¹` half of the re-frozen coefficient class at work: `∇·(a∇w)` is
the continuous compactly supported function `coeffFluxDiv a w`, `w` solves the
massive equation with that forcing on every cube
(`isMassiveWeakSolutionOn_ofContDiff`), and whole-space uniqueness
(`eq_zero_of_localMassiveWeakSolution_of_tendsto_cocompact`) identifies the two
solutions. -/
theorem solution_eq_of_contDiff_compactSupport {a : Vec d → ℝ}
    (hcont : Continuous a) (hpos : ∀ x, 0 < a x) (hc1 : ContDiff ℝ 1 a)
    {DYd : C0ResolventDatum (Vec d)}
    (hY : IsWeakEllipticResolvent a (fun _ ↦ (1 : ℝ)) DYd)
    (mu : PositiveShift) {w : Vec d → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwsupp : HasCompactSupport w) (F : C₀(Vec d, ℝ))
    (hF : ∀ x, F x = (mu : ℝ) * w x - coeffFluxDiv a w x) (x : Vec d) :
    DYd.solution mu F x = w x := by
  set B := divergenceCubeBounds hcont hpos with hB
  set g := DYd.solution mu F with hg
  have hzero : ∀ y, g y - w y = 0 := by
    refine eq_zero_of_localMassiveWeakSolution_of_tendsto_cocompact B mu.property
      (u := fun y ↦ g y - w y) (g.continuous.sub hw.continuous) ?_ ?_
    · simpa using (zero_at_infty g).sub hwsupp.is_zero_at_infty
    · intro k
      set W := cube d (k : ℤ) with hWdef
      have hW := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
      have hWmeas : MeasurableSet W := hW.isOpen.measurableSet
      obtain ⟨v, hv, hvsol⟩ := hY mu F W hW
      have hsmooth :
          IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) (mu : ℝ) W
            (H1Function.ofContDiff hW.isOpen (hw.of_le (by simp)) hwsupp)
            (fun y ↦ F y) := by
        refine IsMassiveWeakSolutionOn.congr_forcing ?_
          (isMassiveWeakSolutionOn_ofContDiff (rho := fun _ ↦ (1 : ℝ)) hc1 hw hwsupp
            hW.isOpen (B.rho_measurable k) (B.rho_bounded k) (fun _ ↦ one_ne_zero))
        funext y
        simp [smoothMassiveForcing, hF y]
      have hsub := IsMassiveWeakSolutionOn.sub (B.ell k) (B.rho_measurable k)
        (B.rho_bounded k) (memL2On_of_zeroAtInfty hW F) (memL2On_of_zeroAtInfty hW F)
        hvsol hsmooth
      refine ⟨v - H1Function.ofContDiff hW.isOpen (hw.of_le (by simp)) hwsupp, ?_,
        IsMassiveWeakSolutionOn.congr_forcing ?_ hsub⟩
      · filter_upwards [ae_restrict_mem hWmeas] with y hy
        simp only [H1Function.sub_toFun, hv y hy]
        rfl
      · funext y
        simp
  have := hzero x
  linarith

/-- **The residual of a classical forcing is compactly supported.**  For
`F = mu w − ∇·(a∇w)` with `w` smooth and compactly supported, the
reciprocal-weighted residual is

`a⁻¹ (mu R^{(a,1)}_mu F − F) = a⁻¹ ∇·(a∇w)` ,

continuous with compact support, hence a `C₀` function.  No decay hypothesis on
`a` or on `a⁻¹` is used: this is the exact point at which the re-frozen
`C^{1,1}_loc` class removes P-220's obstruction `(C0)` on a supply of data. -/
theorem exists_c0_residual_of_contDiff_compactSupport {a : Vec d → ℝ}
    (hcont : Continuous a) (hpos : ∀ x, 0 < a x) (hc1 : ContDiff ℝ 1 a)
    {DYd : C0ResolventDatum (Vec d)}
    (hY : IsWeakEllipticResolvent a (fun _ ↦ (1 : ℝ)) DYd)
    (mu : PositiveShift) {w : Vec d → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwsupp : HasCompactSupport w) (F : C₀(Vec d, ℝ))
    (hF : ∀ x, F x = (mu : ℝ) * w x - coeffFluxDiv a w x) :
    ∃ k : C₀(Vec d, ℝ), ∀ x,
      k x = (a x)⁻¹ * ((mu : ℝ) * DYd.solution mu F x - F x) := by
  have hkcont : Continuous fun x ↦ (a x)⁻¹ * coeffFluxDiv a w x :=
    (hcont.inv₀ fun x ↦ (hpos x).ne').mul (continuous_coeffFluxDiv hc1 hw)
  have hksupp : HasCompactSupport fun x ↦ (a x)⁻¹ * coeffFluxDiv a w x := by
    refine HasCompactSupport.intro hwsupp fun x hx ↦ ?_
    rw [coeffFluxDiv_eq_zero_of_notMem hx, mul_zero]
  refine ⟨compactSupportToC0 (toCompactSupportMap _ hkcont hksupp), fun x ↦ ?_⟩
  rw [compactSupportToC0_apply, toCompactSupportMap_apply,
    solution_eq_of_contDiff_compactSupport hcont hpos hc1 hY mu hw hwsupp F hF x, hF x]
  ring

/-! ### The core hypothesis `(K)` -/

/-- **The classical forcings of smooth compactly supported functions.**  The set
`{mu w − ∇·(a∇w) : w ∈ C_c^∞}` of `C₀` data, whose `(a,1)` resolvent is `w`
itself.  `Dense (SmoothForcing a mu)` is the statement that `C_c^∞` is a core
for the `C₀` generator `L_Y = ∇·(a∇)` of the `(a,1)` diffusion. -/
def SmoothForcing (a : Vec d → ℝ) (mu : ℝ) : Set C₀(Vec d, ℝ) :=
  {F | ∃ w : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) w ∧ HasCompactSupport w ∧
    ∀ x, F x = mu * w x - coeffFluxDiv a w x}

/-- **The classical forcings carry the `C₀` residual.**  Every element of
`SmoothForcing a mu` lies in the set of data of P-223's `(C0′)`. -/
theorem smoothForcing_subset_c0Residual {a : Vec d → ℝ}
    (hcont : Continuous a) (hpos : ∀ x, 0 < a x) (hc1 : ContDiff ℝ 1 a)
    {DYd : C0ResolventDatum (Vec d)}
    (hY : IsWeakEllipticResolvent a (fun _ ↦ (1 : ℝ)) DYd) (mu : PositiveShift) :
    SmoothForcing a (mu : ℝ) ⊆
      {F : C₀(Vec d, ℝ) | ∃ k : C₀(Vec d, ℝ), ∀ x,
        k x = (a x)⁻¹ * ((mu : ℝ) * DYd.solution mu F x - F x)} := by
  rintro F ⟨w, hw, hwsupp, hF⟩
  exact exists_c0_residual_of_contDiff_compactSupport hcont hpos hc1 hY mu hw hwsupp F hF



theorem isIntrinsicTimeChange_of_clockDivergence_of_denseSmoothForcing
    {Theta : Type*} [MeasurableSpace Theta] {d : ℕ}
    (a : Theta → State d → ℝ)
    (ha_pos : ∀ theta x, 0 < a theta x) (ha_cont : ∀ theta, Continuous (a theta))
    (ha_c1 : ∀ theta, ContDiff ℝ 1 (a theta))
    {DXDatum DYDatum : Theta →
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (State d)}
    (DX : GeneratedDiffusionFamily Theta d a a DXDatum)
    (DY : GeneratedDiffusionFamily Theta d a (fun _ _ ↦ 1) DYDatum)
    (PX : CemeteryDiffusion d DX) (PY : CemeteryDiffusion d DY)
    (default : Theta → ContinuousPath (State d))
    (hdense : ∀ (theta : Theta) (mu : MarkovProcess.Semigroup.PositiveShift),
      Dense (SmoothForcing (a theta) (mu : ℝ)))
    (hunbounded : ∀ theta y, ∀ᵐ omega ∂
      ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess
        DX.semigroup DX.conservative (theta, y),
      omega ∈ timeChangeUnboundedEvent a theta) :
    IsIntrinsicTimeChange a
      (Kernel.toLifetimePathKernel PX.law)
      (Kernel.toLifetimePathKernel PY.law) := by
  refine isIntrinsicTimeChange_of_clockDivergence_of_denseC0Residual a ha_pos ha_cont
    DX DY PX PY default (fun theta mu ↦ ?_) hunbounded
  exact (hdense theta mu).mono
    (smoothForcing_subset_c0Residual (ha_cont theta) (ha_pos theta) (ha_c1 theta)
      (DY.weakResolvent theta) mu)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
