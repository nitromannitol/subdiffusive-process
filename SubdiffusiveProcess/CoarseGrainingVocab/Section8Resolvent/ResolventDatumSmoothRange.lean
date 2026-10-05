module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumSmoothSolution
public import Mathlib.Geometry.Manifold.SmoothApprox

@[expose] public section

/-!
# The range of the massive resolvent is dense in `C₀`

(`ResolventDatumDenseRange.lean`) reduced the frozen Section 8 resolvent datum
to two analytic inputs per coefficient pair: decay at
infinity for compactly supported data (R5), and
`HasDenseMassiveResolventRange`, the density of the range of one resolvent.  It
recorded the second as needing a De Giorgi--Nash--Moser local sup bound
(-N1).

That is not so.  Density of the range needs no regularity theory at all, only
the *classical* direction of the equation:

> for `w` smooth and compactly supported, `F := μ w − ρ⁻¹ ∇·(c ∇w)` is a
> continuous compactly supported datum, `w` solves the massive equation with
> forcing `F` on every cube (`ResolventDatumSmoothSolution.lean`), and the
> proved whole-space uniqueness
> `eq_zero_of_localMassiveWeakSolution_of_tendsto_cocompact` identifies
> `R_μ F = w`.

So the range of `R_μ` *contains* every smooth compactly supported function, and
those are dense in `C₀`: the value truncation `compactSupportApprox` of
`C0CompactSupportExtension.lean` reduces to a compactly supported continuous
datum, and Mathlib's `Continuous.exists_contDiff_approx` smooths it in the sup
norm without enlarging its support.

The regularity actually used is that `c` is `C¹` and `ρ` is continuous and
positive.  Both hold for the development's pairs, because the anchored potential
field carries a continuous, locally Lipschitz derivative
(`SubdiffusiveProcess.Model.PotentialField.contDiff_one`).

## Main declarations

* `exists_contDiff_compactSupport_norm_sub_lt` — density of `C_c^∞` in `C₀`.
* `smoothForcingC0` — the datum whose whole-space solution is a prescribed `w`.
* `sol_smoothForcingC0` — `R_μ (μ w − ρ⁻¹ ∇·(c∇w)) = w`.
* `hasDenseMassiveResolventRange_of_contDiff` — the obligation, discharged.


-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open MarkovProcess MarkovProcess.Semigroup
open scoped ZeroAtInfty CompactlySupported

noncomputable section

variable {d : ℕ}

/-! ### Smooth compactly supported functions are dense in `C₀` -/

/-- Package a smooth compactly supported function as a compactly supported
continuous datum. -/
def toCompactSupportMap (v : Vec d → ℝ) (hvc : Continuous v)
    (hvs : HasCompactSupport v) : C_c(Vec d, ℝ) where
  toFun := v
  continuous_toFun := hvc
  hasCompactSupport' := hvs

@[simp]
theorem toCompactSupportMap_apply (v : Vec d → ℝ) (hvc : Continuous v)
    (hvs : HasCompactSupport v) (x : Vec d) : toCompactSupportMap v hvc hvs x = v x := rfl

/-- **Smooth compactly supported functions are dense in `C₀(ℝᵈ, ℝ)`.**  The
value truncation `compactSupportApprox` of `C0CompactSupportExtension.lean`
reduces to a compactly supported *continuous* datum, and Mathlib's
`Continuous.exists_contDiff_approx` smooths it without enlarging its support. -/
theorem exists_contDiff_compactSupport_norm_sub_lt (g : C₀(Vec d, ℝ)) {eps : ℝ}
    (heps : 0 < eps) :
    ∃ h : C_c(Vec d, ℝ), ContDiff ℝ (⊤ : ℕ∞) (h : Vec d → ℝ) ∧
      ‖compactSupportToC0 h - g‖ < eps := by
  classical
  set delta : ℝ := eps / 3 with hdelta_def
  have hdelta : 0 < delta := by positivity
  set h0 : C_c(Vec d, ℝ) := compactSupportApprox g delta hdelta with hh0
  have h0norm : ‖compactSupportToC0 h0 - g‖ ≤ delta :=
    norm_compactSupportApprox_sub_le g delta hdelta
  obtain ⟨v, hv, hvapprox, hvsupp⟩ :=
    (map_continuous h0).exists_contDiff_approx (⊤ : ℕ∞) (ε := fun _ ↦ delta)
      continuous_const (fun _ ↦ hdelta)
  have hvcs : HasCompactSupport v := h0.hasCompactSupport'.mono hvsupp
  refine ⟨toCompactSupportMap v hv.continuous hvcs, hv, ?_⟩
  have hstep : ‖compactSupportToC0 (toCompactSupportMap v hv.continuous hvcs) -
      compactSupportToC0 h0‖ ≤ delta := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    refine (BoundedContinuousFunction.norm_le hdelta.le).2 fun x ↦ ?_
    simp only [ZeroAtInftyContinuousMap.toBCF_apply,
      ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply, compactSupportToC0_apply,
      toCompactSupportMap_apply, Real.norm_eq_abs]
    have := hvapprox x
    rw [Real.dist_eq] at this
    exact this.le
  have hsum : ‖compactSupportToC0 (toCompactSupportMap v hv.continuous hvcs) - g‖ ≤
      delta + delta := by
    have hsplit :
        compactSupportToC0 (toCompactSupportMap v hv.continuous hvcs) - g =
          (compactSupportToC0 (toCompactSupportMap v hv.continuous hvcs) -
            compactSupportToC0 h0) + (compactSupportToC0 h0 - g) := by
      abel
    calc ‖compactSupportToC0 (toCompactSupportMap v hv.continuous hvcs) - g‖
        ≤ ‖compactSupportToC0 (toCompactSupportMap v hv.continuous hvcs) -
            compactSupportToC0 h0‖ + ‖compactSupportToC0 h0 - g‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ delta + delta := add_le_add hstep h0norm
  calc ‖compactSupportToC0 (toCompactSupportMap v hv.continuous hvcs) - g‖
      ≤ delta + delta := hsum
    _ < eps := by rw [hdelta_def]; linarith

/-! ### The forcing whose whole-space solution is a prescribed smooth datum -/

variable {c rho : Vec d → ℝ}

/-- Strict positivity of the weight, from the local cube bounds. -/
theorem MassiveCubeBounds.weight_pos (B : MassiveCubeBounds c rho) (x : Vec d) :
    0 < rho x := by
  obtain ⟨n, hn⟩ := exists_nat_cube_superset (Bornology.isBounded_singleton (x := x))
  exact lt_of_lt_of_le (B.rhoMin_pos n) (B.rho_lower n x (hn rfl))

/-- The compactly supported datum `μ w − ρ⁻¹ ∇·(c∇w)`. -/
def smoothForcingCc (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c)
    (hrho : Continuous rho) (mu : ℝ) {w : Vec d → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwsupp : HasCompactSupport w) : C_c(Vec d, ℝ) where
  toFun := smoothMassiveForcing c rho mu w
  continuous_toFun :=
    (continuous_const.mul hw.continuous).sub
      ((continuous_coeffFluxDiv hc hw).div hrho (fun y ↦ (B.weight_pos y).ne'))
  hasCompactSupport' := by
    refine HasCompactSupport.intro hwsupp fun x hx ↦ ?_
    have hw0 : w x = 0 := image_eq_zero_of_notMem_tsupport hx
    have hd0 : coeffFluxDiv c w x = 0 := coeffFluxDiv_eq_zero_of_notMem hx
    simp [smoothMassiveForcing, hw0, hd0]

@[simp]
theorem smoothForcingCc_apply (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c)
    (hrho : Continuous rho) (mu : ℝ) {w : Vec d → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwsupp : HasCompactSupport w) (x : Vec d) :
    smoothForcingCc B hc hrho mu hw hwsupp x = smoothMassiveForcing c rho mu w x := rfl

/-- The same datum as an element of `C₀`. -/
def smoothForcingC0 (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c)
    (hrho : Continuous rho) (mu : ℝ) {w : Vec d → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwsupp : HasCompactSupport w) : C₀(Vec d, ℝ) :=
  compactSupportToC0 (smoothForcingCc B hc hrho mu hw hwsupp)

@[simp]
theorem smoothForcingC0_apply (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c)
    (hrho : Continuous rho) (mu : ℝ) {w : Vec d → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwsupp : HasCompactSupport w) (x : Vec d) :
    smoothForcingC0 B hc hrho mu hw hwsupp x = smoothMassiveForcing c rho mu w x := rfl

/-- **A smooth compactly supported function is in the range of the resolvent.**
Its preimage is the classical datum `μ w − ρ⁻¹ ∇·(c∇w)`, which is continuous and
compactly supported, hence a legitimate `C₀` datum; whole-space uniqueness
identifies the solution with `w`. -/
theorem sol_smoothForcingC0 [NeZero d] (B : MassiveCubeBounds c rho)
    (hc : ContDiff ℝ 1 c) (hrho : Continuous rho)
    (R : MassiveC0Resolvent c rho) (mu : PositiveShift)
    {w : Vec d → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwsupp : HasCompactSupport w) (x : Vec d) :
    R.sol mu (smoothForcingC0 B hc hrho (mu : ℝ) hw hwsupp) x = w x := by
  classical
  set F : C₀(Vec d, ℝ) := smoothForcingC0 B hc hrho (mu : ℝ) hw hwsupp with hF
  set u : Vec d → ℝ := fun y ↦ R.sol mu F y - w y with hu
  have hrhoNe : ∀ y, rho y ≠ 0 := fun y ↦ (B.weight_pos y).ne'
  have hcont : Continuous u := (map_continuous (R.sol mu F)).sub hw.continuous
  have hdecay : Tendsto u (cocompact (Vec d)) (nhds 0) := by
    have h1 : Tendsto (fun y ↦ R.sol mu F y) (cocompact (Vec d)) (nhds 0) :=
      zero_at_infty (R.sol mu F)
    have h2 : Tendsto w (cocompact (Vec d)) (nhds 0) := hwsupp.is_zero_at_infty
    simpa using h1.sub h2
  have hFL2 : ∀ k : ℕ, MemL2On (cube d (k : ℤ)) (fun y ↦ F y) :=
    fun k ↦ ((map_continuous F).memLp_of_hasCompactSupport
      (smoothForcingCc B hc hrho (mu : ℝ) hw hwsupp).hasCompactSupport').restrict _
  have hlocal : ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      v.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        IsMassiveWeakSolutionOn c rho (mu : ℝ) (cube d (k : ℤ)) v (fun _ ↦ (0 : ℝ)) := by
    intro k
    obtain ⟨vk, hvkfun, hvksol⟩ := R.sol_local mu F k
    have hWdom := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
    have hsmooth : IsMassiveWeakSolutionOn c rho (mu : ℝ) (cube d (k : ℤ))
        (H1Function.ofContDiff hWdom.isOpen (hw.of_le (by simp)) hwsupp)
        (smoothMassiveForcing c rho (mu : ℝ) w) :=
      isMassiveWeakSolutionOn_ofContDiff hc hw hwsupp hWdom.isOpen
        (B.rho_measurable k) (B.rho_bounded k) hrhoNe
    have hsub := IsMassiveWeakSolutionOn.sub (B.ell k) (B.rho_measurable k)
      (B.rho_bounded k) (hFL2 k) (hFL2 k) hvksol hsmooth
    refine ⟨vk - H1Function.ofContDiff hWdom.isOpen (hw.of_le (by simp)) hwsupp, ?_, ?_⟩
    · refine Filter.Eventually.of_forall fun y ↦ ?_
      rw [H1Function.sub_toFun]
      show vk.toFun y - w y = u y
      rw [hvkfun y]
    · refine IsMassiveWeakSolutionOn.congr_forcing ?_ hsub
      funext y
      simp
  have hzero := eq_zero_of_localMassiveWeakSolution_of_tendsto_cocompact B mu.2 hcont
    hdecay hlocal x
  have : R.sol mu F x - w x = 0 := hzero
  linarith

/-! ### Dense range -/

/-- **The range of the massive resolvent is dense in `C₀`.**  Every smooth
compactly supported function lies in the range (`sol_smoothForcingC0`), and
those are dense (`exists_contDiff_compactSupport_norm_sub_lt`).  No local sup
bound, no barrier and no De Giorgi--Nash--Moser estimate is needed: the only
regularity used is that `c` is `C¹` and `ρ` is continuous and positive, which
holds for the development's pairs because the anchored potential field is locally
`C^{1,1}`. -/
theorem hasDenseMassiveResolventRange_of_contDiff [NeZero d]
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c) (hrho : Continuous rho) :
    HasDenseMassiveResolventRange c rho := by
  intro R nu
  rw [Metric.denseRange_iff]
  intro g eps heps
  obtain ⟨h, hsmooth, hnorm⟩ := exists_contDiff_compactSupport_norm_sub_lt g heps
  refine ⟨smoothForcingC0 B hc hrho (nu : ℝ) hsmooth h.hasCompactSupport', ?_⟩
  have hsol : R.sol nu (smoothForcingC0 B hc hrho (nu : ℝ) hsmooth h.hasCompactSupport')
      = compactSupportToC0 h := by
    ext x
    exact sol_smoothForcingC0 B hc hrho R nu hsmooth h.hasCompactSupport' x
  rw [hsol, dist_eq_norm, norm_sub_rev]
  exact hnorm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
