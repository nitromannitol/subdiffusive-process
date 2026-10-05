module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsExterior

@[expose] public section

/-!
# The tested identity and the mesoscopic optimisation of `l.local.L2.resolvent`

 states the local `L²` estimate for the
resolvent with **coarse-grained** ellipticity constants,

```
t ℓ⁻² Λ_{1/16}^{12}(Q;a) λ_{1/16}^{-11}(Q;a) ≤ C⁻¹ η^{15/2}
  ⟹ ‖u‖²_{L̲²(Q/3)} + t ‖a^{1/2}∇u‖²_{L̲²(Q/3)}
       ≤ C η (‖u‖²_{L̲²(Q)} + ℓ⁴ λ_{1/16}^{-2}(Q;a) ‖g‖²_{L̲²(Q)}),
```

and proves it in two steps: an intermediate display obtained from the tested
identity, the two `[AK.HC]` Besov inequalities, the coarse-grained Poincaré and
Caccioppoli inequalities, *"optimized in the mesoscopic scale"*, and Dirichlet
`H²` regularity; and then a final Young step which converts that display into
the conclusion using the smallness condition.

This file contributes the parts of that proof which are independent of the
Besov machinery:

* `massive_cutoff_tested_identity` — the tested identity itself, in the
  **cross form**
  `mu ∫ χ²u² + ∫ a χ²|∇u|² + 2∫ a χ u (∇u·∇χ) = ∫ f χ² u`.
  `massive_cutoff_mass_energy_le_of_zero_forcing` proves only the
  Young-inequality *consequence* of this identity, in which the cross term has
  already been thrown against `∫ a u²|∇χ|²` — the coefficient-weighted mass
  which coarse-grained ellipticity does **not** control.  Every coarse route
  has to price the cross term by duality instead, so it needs the identity.
* `massive_local_l2_contraction_of_cross_bound` — the contraction that any such
  price yields.
* `mesoscopic_mass_contraction` — the **mesoscopic optimisation** in the
  abstract: a cross-term price with a free mesoscopic parameter `β ∈ (0,1]`
  of the shape `β P E + β⁻¹ R √E √M + β S t⁻¹ M`, together with a coarse energy
  bound `t E ≤ Γ M`, gives the contraction `m + t e ≤ η M` as soon as
  `81 (P Γ + S)² R² Γ t ≤ η⁴`.  The optimal `β` is `η/(3 (P Γ + S))`, and
  `mesoscopic_smallness_of_paper_condition` derives that smallness from the
  manuscript's `t ℓ⁻² Λ^{12} λ^{-11} ≤ C⁻¹ η^{15/2}`.
* `whole_cube_price_insufficient` — the endpoint `β = 1` of the price (the
  proved whole-cube pairing) provably yields **no** contraction factor below
  `P Γ ≥ 1`, however small `t` is.  The free mesoscopic parameter is therefore
  not a convenience.
* `localL2_resolvent_of_display` — the manuscript's final step, verbatim:
  the intermediate display of `11455-11460` plus the smallness condition
  `11446-11449` give `e.local.L2.resolvent`.
* `localL2_resolvent_coarse_translatedCube_contraction` and its carrier-level
  form `wholeSpaceSolution_cell_coarse_mass_contraction` — the coarse-grained
  counterparts of `localL2_resolvent_translatedCube_contraction`, conditional on
  exactly two named inputs: `MesoscopicCrossPrice` and `CoarseEnergyBound`.
* `wholeSpaceSolution_exterior_decay_of_cell_mass_contractions` — the exterior
  row's geometry consuming a per-cell mass contraction instead of the `L^∞`
  smallness condition, so that either route feeds it.

## References

*  (`l.local.L2.resolvent`);
*  (the centred-enlargement form).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-! ### The tested identity -/

/-- The differential of a square, evaluated on a coordinate direction. -/
private theorem fderiv_sq_apply_meso {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec d) (i : Fin d) :
    (fderiv ℝ (fun y ↦ f y ^ 2) x) (basisVec i) =
      2 * f x * (fderiv ℝ f x) (basisVec i) := by
  have hdiff : DifferentiableAt ℝ f x :=
    hf.differentiable (by simp) x
  have h := (hdiff.hasFDerivAt).pow 2
  rw [h.fderiv]
  simp [mul_comm, mul_assoc]

/-- **The tested identity for the massive equation.**

If `u` solves `mu u − ∇·(a ∇u) = f` weakly on a bounded open convex domain `W`
and `chi` is a smooth cutoff compactly supported in `W`, then testing with
`chi² u` gives

```
mu ∫_W chi² u² + ∫_W a chi² |∇u|² + 2 ∫_W a chi u (∇u · ∇chi) = ∫_W f chi² u .
```

This is the identity behind  (*"Test with
`φ u`, where `φ = 1` on the middle third"*).  `massive_cutoff_mass_energy_le_of_zero_forcing` proves only the consequence of
this identity after the cross term has been thrown by Young's inequality
against `∫ a u² |∇chi|²`; that step is fatal for the coarse-grained form of
the local `L²` resolvent estimate, because `Lambda_{1/16}` gives no control of a
coefficient-weighted *mass*.  The identity keeps the cross term in the shape a
duality price consumes. -/
theorem massive_cutoff_tested_identity
    {a f : Vec d → ℝ} {mu lam Lam K : ℝ} {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a))
    (u : H1Function W)
    (hu : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu W u f)
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi) (hchiS : tsupport chi ⊆ W)
    (hchi_le : ∀ x, |chi x| ≤ 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K) :
    mu * ∫ x in W, chi x ^ 2 * u.toFun x ^ 2 ∂volume +
        (∫ x in W, a x * chi x ^ 2 * vecNormSq (u.grad x) ∂volume +
          2 * ∫ x in W, a x * chi x * u.toFun x *
            vecDot (u.grad x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume) =
      ∫ x in W, f x * chi x ^ 2 * u.toFun x ∂volume := by
  classical
  set gchi : Vec d → Vec d := fun x i ↦ (fderiv ℝ chi x) (basisVec i) with hgchi_def
  have hK0 : (0 : ℝ) ≤ K := le_trans (vecNormSq_nonneg _) (hK 0)
  have hgchi_cont : Continuous gchi := by
    refine continuous_pi fun i ↦ ?_
    exact ((hchi.continuous_fderiv (by simp)).clm_apply
      continuous_const)
  have hgchi_norm : ∀ x, ‖gchi x‖ ≤ Real.sqrt K := by
    intro x
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg K)).mpr fun i ↦ ?_
    have h1 : gchi x i ^ (2 : ℕ) ≤ K :=
      le_trans (sq_apply_le_vecNormSq (gchi x) i) (hK x)
    calc ‖gchi x i‖ = Real.sqrt (gchi x i ^ (2 : ℕ)) := by
          rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
      _ ≤ Real.sqrt K := Real.sqrt_le_sqrt h1
  have hchi_sq_le : ∀ x, chi x ^ 2 ≤ 1 := by
    intro x
    have := hchi_le x
    nlinarith [abs_nonneg (chi x), sq_abs (chi x)]
  -- the test function `chi² u`
  set eta : Vec d → ℝ := fun x ↦ chi x ^ 2 with heta_def
  have heta : ContDiff ℝ (⊤ : ℕ∞) eta := hchi.pow 2
  have hetaC : HasCompactSupport eta := by
    apply HasCompactSupport.intro hchiC.isCompact
    intro x hx
    have : chi x = 0 := by
      by_contra hne
      exact hx (subset_closure hne)
    simp [heta_def, this]
  have hetaS : tsupport eta ⊆ W := by
    refine le_trans (closure_mono ?_) hchiS
    intro x hx
    simp only [heta_def, Function.mem_support, ne_eq] at hx ⊢
    exact fun h ↦ hx (by simp [h])
  set phi : H10Function W :=
    u.mulContDiffHasCompactSupportToH10 hW heta hetaC hetaS with hphi_def
  have hphi_toFun : phi.toH1Function.toFun = fun x ↦ eta x * u.toFun x :=
    H1Function.mulContDiffHasCompactSupportToH10_toFun u hW heta hetaC hetaS
  set psi : H1Function W := u.mulContDiffHasCompactSupport heta hetaC with hpsi_def
  have hpsi_toFun : psi.toFun = fun x ↦ eta x * u.toFun x := by simp [hpsi_def]
  have hpsi_grad : psi.grad =
      fun x i ↦ eta x * u.grad x i + u.toFun x * (fderiv ℝ eta x) (basisVec i) := by
    simp [hpsi_def]
  have hgrad : phi.toH1Function.grad =ᵐ[volume.restrict W] psi.grad := by
    refine Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq hW.isOpen ?_
    filter_upwards with x
    rw [hphi_toFun, hpsi_toFun]
  have heq := hu phi
  -- the two vector fields the gradient of the test function splits into
  set V1 : Vec d → Vec d := fun x ↦ (chi x ^ 2) • u.grad x with hV1_def
  set V2 : Vec d → Vec d := fun x ↦ (2 * chi x * u.toFun x) • gchi x with hV2_def
  have hpsi_split : ∀ x, psi.grad x = fun i ↦ V1 x i + V2 x i := by
    intro x
    rw [hpsi_grad]
    funext i
    simp only [heta_def, hgchi_def, hV1_def, hV2_def, Pi.smul_apply, smul_eq_mul,
      fderiv_sq_apply_meso hchi x i]
    ring
  have hV1meas : AEStronglyMeasurable V1 (volume.restrict W) := by
    have := ((hchi.continuous.pow 2).aestronglyMeasurable
      (μ := volume.restrict W)).smul u.grad_memVectorL2.aestronglyMeasurable
    simpa [hV1_def] using! this
  have hV2meas : AEStronglyMeasurable V2 (volume.restrict W) := by
    have hscal : AEStronglyMeasurable (fun x ↦ 2 * chi x * u.toFun x)
        (volume.restrict W) := by
      have hc : Continuous fun x : Vec d ↦ 2 * chi x :=
        continuous_const.mul hchi.continuous
      exact (hc.aestronglyMeasurable).mul u.memL2.aestronglyMeasurable
    have := hscal.smul (hgchi_cont.aestronglyMeasurable (μ := volume.restrict W))
    simpa [hV2_def] using! this
  have hV1mem : MemVectorL2 W V1 := by
    refine MemLp.mono u.grad_memVectorL2 hV1meas ?_
    filter_upwards with x
    rw [hV1_def]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (chi x))]
    nlinarith [norm_nonneg (u.grad x), hchi_sq_le x, sq_nonneg (chi x)]
  have hV2mem : MemVectorL2 W V2 := by
    refine MemLp.mono (u.memL2.const_mul (2 * Real.sqrt K)) hV2meas ?_
    filter_upwards with x
    rw [hV2_def]
    have hgn := hgchi_norm x
    have h1 : |chi x| ≤ 1 := hchi_le x
    have habs : ‖(2 * chi x * u.toFun x) • gchi x‖ =
        2 * |chi x| * |u.toFun x| * ‖gchi x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul]
      norm_num
    have hrhs : ‖2 * Real.sqrt K * u.toFun x‖ = 2 * Real.sqrt K * |u.toFun x| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg K)]
      norm_num
    rw [habs, hrhs]
    have h2 : (0 : ℝ) ≤ |u.toFun x| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ ‖gchi x‖ := norm_nonneg _
    have step1 : 2 * |chi x| * |u.toFun x| ≤ 2 * |u.toFun x| := by
      nlinarith [abs_nonneg (chi x)]
    have step2 : 2 * |chi x| * |u.toFun x| * ‖gchi x‖ ≤ 2 * |u.toFun x| * ‖gchi x‖ :=
      mul_le_mul_of_nonneg_right step1 h3
    have step3 : 2 * |u.toFun x| * ‖gchi x‖ ≤ 2 * |u.toFun x| * Real.sqrt K :=
      mul_le_mul_of_nonneg_left hgn (by positivity)
    nlinarith [step2, step3]
  -- the two scalar densities
  have hA1int : IntegrableOn
      (fun x ↦ a x * chi x ^ 2 * vecNormSq (u.grad x)) W :=
    integrableOn_cutoff_energy hW.isOpen.measurableSet hEll u
      hchi.continuous.aestronglyMeasurable hchi_le
  have hA1eq : ∀ x, vecDot (a x • u.grad x) (V1 x) =
      a x * chi x ^ 2 * vecNormSq (u.grad x) := by
    intro x
    simp only [hV1_def, vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hA2eq : ∀ x, vecDot (a x • u.grad x) (V2 x) =
      2 * (a x * chi x * u.toFun x * vecDot (u.grad x) (gchi x)) := by
    intro x
    simp only [hV2_def, vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hA2int : IntegrableOn
      (fun x ↦ a x * chi x * u.toFun x * vecDot (u.grad x) (gchi x)) W := by
    have hbase : IntegrableOn (fun x ↦ vecDot (a x • u.grad x) (V2 x)) W :=
      integrableOn_energy_term hEll u.grad_memVectorL2 hV2mem
    have := (hbase.congr (Filter.Eventually.of_forall hA2eq)).const_mul (2 : ℝ)⁻¹
    refine this.congr ?_
    filter_upwards with x
    ring
  -- expand the energy pairing
  have hsplit : ∫ x in W, vecDot (a x • u.grad x) (psi.grad x) ∂volume =
      (∫ x in W, a x * chi x ^ 2 * vecNormSq (u.grad x) ∂volume) +
        2 * ∫ x in W, a x * chi x * u.toFun x * vecDot (u.grad x) (gchi x) ∂volume := by
    have hpt : ∀ x, vecDot (a x • u.grad x) (psi.grad x) =
        (a x * chi x ^ 2 * vecNormSq (u.grad x)) +
          2 * (a x * chi x * u.toFun x * vecDot (u.grad x) (gchi x)) := by
      intro x
      rw [hpsi_split x]
      have hbil : vecDot (a x • u.grad x) (fun i ↦ V1 x i + V2 x i) =
          vecDot (a x • u.grad x) (V1 x) + vecDot (a x • u.grad x) (V2 x) := by
        simp only [vecDot, mul_add]
        exact Finset.sum_add_distrib
      rw [hbil, hA1eq x, hA2eq x]
    calc ∫ x in W, vecDot (a x • u.grad x) (psi.grad x) ∂volume
        = ∫ x in W, ((a x * chi x ^ 2 * vecNormSq (u.grad x)) +
            2 * (a x * chi x * u.toFun x * vecDot (u.grad x) (gchi x))) ∂volume := by
          exact integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = (∫ x in W, a x * chi x ^ 2 * vecNormSq (u.grad x) ∂volume) +
            ∫ x in W, 2 * (a x * chi x * u.toFun x * vecDot (u.grad x) (gchi x)) ∂volume :=
          integral_add hA1int (hA2int.const_mul 2)
      _ = _ := by rw [integral_const_mul]
  -- rewrite the three terms of the weak formulation
  have hmass : ∫ x in W, (fun _ ↦ (1 : ℝ)) x * u.toFun x * phi.toH1Function.toFun x ∂volume =
      ∫ x in W, chi x ^ 2 * u.toFun x ^ 2 ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [hphi_toFun]
    simp only [heta_def]
    ring
  have hforce : ∫ x in W, (fun _ ↦ (1 : ℝ)) x * f x * phi.toH1Function.toFun x ∂volume =
      ∫ x in W, f x * chi x ^ 2 * u.toFun x ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [hphi_toFun]
    simp only [heta_def]
    ring
  have henergy : ∫ x in W, vecDot (a x • u.grad x) (phi.toH1Function.grad x) ∂volume =
      ∫ x in W, vecDot (a x • u.grad x) (psi.grad x) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hgrad] with x hx
    rw [hx]
  rw [hmass, hforce, henergy, hsplit] at heq
  linarith [heq]

/-! ### The contraction produced by a cross-term price -/

/-- **The local contraction from any price for the cross term.**

If `u` solves `t⁻¹ u − ∇·(a ∇u) = f` weakly on `W`, `S ⊆ W` carries a cutoff
`chi` which is `1` on `S` and compactly supported in `W`, and the cross term and
the forcing pairing of the tested identity are bounded by `B` and `D`, then

```
t⁻¹ ∫_S u² + ∫_S a |∇u|² ≤ B + D .
```

This is the interface at which the coarse-grained cross-term price enters.  Taking the crude bound
`B = 2 Lam K ∫_W u²` (Cauchy–Schwarz and `a ≤ Lam`) recovers `massive_local_l2_contraction_of_cutoff` up to the constant; the point of the
manuscript's proof is to price `B` by Besov duality, with **coarse-grained**
constants and no `L^∞` bound on `a`. -/
theorem massive_cutoff_mass_energy_le_of_cross_bound
    {a f : Vec d → ℝ} {lam Lam t K B D : ℝ} {W S : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (ht : 0 < t)
    (hSW : S ⊆ W) (hSmeas : MeasurableSet S)
    (u : H1Function W)
    (hu : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹ W u f)
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi) (hchiS : tsupport chi ⊆ W)
    (hchi_le : ∀ x, |chi x| ≤ 1) (hchi_one : ∀ x ∈ S, chi x = 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K)
    (hcross : |2 * ∫ x in W, a x * chi x * u.toFun x *
        vecDot (u.grad x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume| ≤ B)
    (hforce : |∫ x in W, f x * chi x ^ 2 * u.toFun x ∂volume| ≤ D) :
    t⁻¹ * (∫ x in S, u.toFun x ^ 2 ∂volume) +
        ∫ x in S, a x * vecNormSq (u.grad x) ∂volume ≤ B + D := by
  classical
  have hWmeas : MeasurableSet W := hW.isOpen.measurableSet
  have hid := massive_cutoff_tested_identity hW hEll u hu hchi hchiC hchiS hchi_le hK
  -- integrability of the two localized densities
  have husq : IntegrableOn (fun x ↦ u.toFun x ^ 2) W := u.memL2.integrable_sq
  have hcutsq : IntegrableOn (fun x ↦ chi x ^ 2 * u.toFun x ^ 2) W := by
    refine Integrable.mono' husq
      ((hchi.continuous.aestronglyMeasurable.pow 2).mul
        husq.aestronglyMeasurable) ?_
    filter_upwards with x
    have h1 : chi x ^ 2 ≤ 1 := by
      have := hchi_le x
      nlinarith [abs_nonneg (chi x), sq_abs (chi x)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (chi x), sq_nonneg (u.toFun x)]
  have hint_chi : IntegrableOn
      (fun x ↦ a x * chi x ^ 2 * vecNormSq (u.grad x)) W :=
    integrableOn_cutoff_energy hWmeas hEll u
      hchi.continuous.aestronglyMeasurable hchi_le
  have hleft1 : ∫ x in S, u.toFun x ^ 2 ∂volume ≤
      ∫ x in W, chi x ^ 2 * u.toFun x ^ 2 ∂volume := by
    have hcongr : ∫ x in S, u.toFun x ^ 2 ∂volume =
        ∫ x in S, chi x ^ 2 * u.toFun x ^ 2 ∂volume := by
      refine setIntegral_congr_fun hSmeas fun x hx ↦ ?_
      rw [hchi_one x hx]
      ring
    rw [hcongr]
    refine setIntegral_mono_set hcutsq ?_ (Filter.Eventually.of_forall hSW)
    filter_upwards with x
    positivity
  have hleft2 : ∫ x in S, a x * vecNormSq (u.grad x) ∂volume ≤
      ∫ x in W, a x * chi x ^ 2 * vecNormSq (u.grad x) ∂volume := by
    have hcongr : ∫ x in S, a x * vecNormSq (u.grad x) ∂volume =
        ∫ x in S, a x * chi x ^ 2 * vecNormSq (u.grad x) ∂volume := by
      refine setIntegral_congr_fun hSmeas fun x hx ↦ ?_
      rw [hchi_one x hx]
      ring
    rw [hcongr]
    refine setIntegral_mono_set hint_chi ?_ (Filter.Eventually.of_forall hSW)
    filter_upwards with x
    have := haNonneg x
    have := vecNormSq_nonneg (u.grad x)
    positivity
  have hcross' := (abs_le.1 hcross).1
  have hforce' := (abs_le.1 hforce).2
  have htinv : (0 : ℝ) < t⁻¹ := inv_pos.mpr ht
  have h1 : t⁻¹ * ∫ x in S, u.toFun x ^ 2 ∂volume ≤
      t⁻¹ * ∫ x in W, chi x ^ 2 * u.toFun x ^ 2 ∂volume :=
    mul_le_mul_of_nonneg_left hleft1 htinv.le
  linarith [hid, h1, hleft2, hcross', hforce']

/-! ### The mesoscopic optimisation -/

/-- **The mesoscopic optimisation.**

Suppose the cross term of the tested identity admits, for every mesoscopic
parameter `β ∈ (0,1]`, the price

```
t⁻¹ m + e ≤ β P E + β⁻¹ R √E √M + β S t⁻¹ M + D ,
```

where `E` is the energy and `M` the mass on the larger cube, and suppose the
coarse energy bound `t E ≤ Γ M` holds.  Then, provided

```
81 (P Γ + S)² R² Γ t ≤ η⁴ ,
```

one has `m + t e ≤ η M + t D`.  The optimal mesoscopic parameter is
`β = η/(3 (P Γ + S))`; the two `β`-terms then contribute exactly `η M / 3`
each, and the `β⁻¹` term is `≤ η M / 3` precisely by the smallness hypothesis.

This is the abstract content of *"optimized in the mesoscopic scale"*
Three features of the shape matter:

* the `β E` term is what the *fluctuation* half of the mesoscopic splitting of
  the positive Besov norm of `chi u ∇chi` produces (`β = (w/ℓ)^{1-s}` with `w`
  the mesoscopic scale), and it is **essential** that `β` is free: `t E` is
  itself of the order of `M`, so a price of the shape `P E` with `P ≥ 1` gives
  no smallness whatever, however small `t` is
  (`whole_cube_price_insufficient` below);
* the `β⁻¹ √E √M` term is the *mean* half of the same splitting, whose constant
  degrades as the mesoscopic scale decreases;
* the `β S t⁻¹ M` term is the remainder left by the Dirichlet `H²` lift of the
  mass term, which the manuscript's
  intermediate display carries as `(η/2) t⁻¹‖u‖₂²`: at unit scale its constant
  is dimensional, and it is the mesoscopic scale — at which the `H¹₀` lift of
  `t⁻¹u` costs only `w t⁻¹‖u‖₂` — that makes it small. -/
theorem mesoscopic_mass_contraction
    {t eta P R S Gam m e E M D : ℝ}
    (ht : 0 < t) (heta : 0 < eta) (hP : 0 < P) (hGam : 0 < Gam) (hR : 0 ≤ R)
    (hS : 0 ≤ S) (hM : 0 ≤ M)
    (hbeta1 : eta ≤ 3 * (P * Gam + S))
    (hprice : ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
      t⁻¹ * m + e ≤ beta * P * E + beta⁻¹ * R * Real.sqrt E * Real.sqrt M +
        beta * S * (t⁻¹ * M) + D)
    (henergy : t * E ≤ Gam * M)
    (hsmall : 81 * (P * Gam + S) ^ 2 * R ^ 2 * Gam * t ≤ eta ^ 4) :
    m + t * e ≤ eta * M + t * D := by
  have hPS : 0 < P * Gam + S := by positivity
  have hPS3 : 0 < 3 * (P * Gam + S) := by positivity
  obtain ⟨beta, hbeta_def⟩ : ∃ b : ℝ, b = eta / (3 * (P * Gam + S)) := ⟨_, rfl⟩
  have hbeta_pos : 0 < beta := by rw [hbeta_def]; positivity
  have hbeta_le : beta ≤ 1 := by
    rw [hbeta_def, div_le_one hPS3]
    exact hbeta1
  have hpr := hprice beta hbeta_pos hbeta_le
  have hbetaPS : beta * (P * Gam + S) = eta / 3 := by
    rw [hbeta_def]
    field_simp
  -- the energy half of the price
  have hfirst : t * (beta * P * E) ≤ eta / 3 * M := by
    have h2 : beta * P * (t * E) ≤ beta * P * (Gam * M) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    have h3 : beta * P * (Gam * M) ≤ (beta * (P * Gam + S)) * M := by
      have hSM : 0 ≤ beta * S * M := by positivity
      nlinarith [hSM]
    calc t * (beta * P * E) = beta * P * (t * E) := by ring
      _ ≤ beta * P * (Gam * M) := h2
      _ ≤ (beta * (P * Gam + S)) * M := h3
      _ = eta / 3 * M := by rw [hbetaPS]
  -- the lift remainder
  have hthird : t * (beta * S * (t⁻¹ * M)) ≤ eta / 3 * M := by
    have hrw : t * (beta * S * (t⁻¹ * M)) = beta * S * M := by
      field_simp
    have hle : beta * S ≤ beta * (P * Gam + S) := by
      have : 0 ≤ beta * (P * Gam) := by positivity
      nlinarith [this]
    rw [hrw, hbetaPS.symm]
    exact mul_le_mul_of_nonneg_right hle hM
  -- the mean half of the price
  have hsqrt : t * Real.sqrt E ≤ Real.sqrt (t * Gam) * Real.sqrt M := by
    have hkey : t ^ 2 * E ≤ t * Gam * M := by nlinarith [henergy, ht.le]
    have hL : t * Real.sqrt E = Real.sqrt (t ^ 2 * E) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ht.le]
    have hR' : Real.sqrt (t * Gam) * Real.sqrt M = Real.sqrt (t * Gam * M) := by
      rw [← Real.sqrt_mul (by positivity)]
    rw [hL, hR']
    exact Real.sqrt_le_sqrt hkey
  have hcoef : beta⁻¹ * R * Real.sqrt (t * Gam) ≤ eta / 3 := by
    have hbinv : beta⁻¹ = 3 * (P * Gam + S) / eta := by
      rw [hbeta_def, inv_div]
    have hsqsq : Real.sqrt (t * Gam) ^ 2 = t * Gam := Real.sq_sqrt (by positivity)
    have hsq : (9 * (P * Gam + S) * R * Real.sqrt (t * Gam)) ^ 2 ≤ (eta ^ 2) ^ 2 := by
      calc (9 * (P * Gam + S) * R * Real.sqrt (t * Gam)) ^ 2
          = 81 * (P * Gam + S) ^ 2 * R ^ 2 * (Real.sqrt (t * Gam) ^ 2) := by ring
        _ = 81 * (P * Gam + S) ^ 2 * R ^ 2 * (t * Gam) := by rw [hsqsq]
        _ = 81 * (P * Gam + S) ^ 2 * R ^ 2 * Gam * t := by ring
        _ ≤ eta ^ 4 := hsmall
        _ = (eta ^ 2) ^ 2 := by ring
    have hnn : (0 : ℝ) ≤ 9 * (P * Gam + S) * R * Real.sqrt (t * Gam) := by positivity
    have hnn2 : (0 : ℝ) ≤ eta ^ 2 := by positivity
    have hle : 9 * (P * Gam + S) * R * Real.sqrt (t * Gam) ≤ eta ^ 2 := by
      nlinarith [hsq, hnn, hnn2]
    rw [hbinv, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ heta]
    nlinarith [hle, heta]
  have hsecond : t * (beta⁻¹ * R * Real.sqrt E * Real.sqrt M) ≤ eta / 3 * M := by
    have hstep : t * (beta⁻¹ * R * Real.sqrt E * Real.sqrt M) =
        beta⁻¹ * R * (t * Real.sqrt E) * Real.sqrt M := by ring
    have h1 : beta⁻¹ * R * (t * Real.sqrt E) * Real.sqrt M ≤
        beta⁻¹ * R * (Real.sqrt (t * Gam) * Real.sqrt M) * Real.sqrt M := by
      have hnn : (0 : ℝ) ≤ beta⁻¹ * R := by positivity
      have := mul_le_mul_of_nonneg_left hsqrt hnn
      exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg M)
    have h2 : beta⁻¹ * R * (Real.sqrt (t * Gam) * Real.sqrt M) * Real.sqrt M =
        (beta⁻¹ * R * Real.sqrt (t * Gam)) * M := by
      have hMM : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM
      calc beta⁻¹ * R * (Real.sqrt (t * Gam) * Real.sqrt M) * Real.sqrt M
          = (beta⁻¹ * R * Real.sqrt (t * Gam)) * (Real.sqrt M * Real.sqrt M) := by ring
        _ = (beta⁻¹ * R * Real.sqrt (t * Gam)) * M := by rw [hMM]
    have h3 : (beta⁻¹ * R * Real.sqrt (t * Gam)) * M ≤ eta / 3 * M :=
      mul_le_mul_of_nonneg_right hcoef hM
    rw [hstep]
    linarith [h1, h2, h3]
  have hmul := mul_le_mul_of_nonneg_left hpr ht.le
  have hexp : t * (t⁻¹ * m + e) = m + t * e := by field_simp
  have hdistr : t * (beta * P * E + beta⁻¹ * R * Real.sqrt E * Real.sqrt M +
      beta * S * (t⁻¹ * M) + D) =
      t * (beta * P * E) + t * (beta⁻¹ * R * Real.sqrt E * Real.sqrt M) +
        t * (beta * S * (t⁻¹ * M)) + t * D := by ring
  rw [hexp, hdistr] at hmul
  linarith [hmul, hfirst, hsecond, hthird]

/-! ### The manuscript's final Young step -/

private theorem localL2_resolvent_young_bound {K eta lam M G : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam) (hM : 0 ≤ M) (hG : 0 ≤ G)
    (hKnn : 0 ≤ K) (hKle : K ≤ eta / lam) :
    K * Real.sqrt M * Real.sqrt G ≤ eta * M + eta / 4 * (lam⁻¹ ^ 2 * G) := by
  have hsqM : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM
  have hsqG : Real.sqrt G * Real.sqrt G = G := Real.mul_self_sqrt hG
  have hx : (0 : ℝ) ≤ Real.sqrt M := Real.sqrt_nonneg M
  have hy : (0 : ℝ) ≤ Real.sqrt G := Real.sqrt_nonneg G
  have hid : eta * (Real.sqrt M * Real.sqrt M) +
      K ^ 2 / (4 * eta) * (Real.sqrt G * Real.sqrt G) -
      K * Real.sqrt M * Real.sqrt G =
      (2 * eta * Real.sqrt M - K * Real.sqrt G) ^ 2 / (4 * eta) := by
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ (2 * eta * Real.sqrt M - K * Real.sqrt G) ^ 2 / (4 * eta) := by
    positivity
  have hbase : K * Real.sqrt M * Real.sqrt G ≤
      eta * (Real.sqrt M * Real.sqrt M) +
        K ^ 2 / (4 * eta) * (Real.sqrt G * Real.sqrt G) := by
    linarith [hid, hnn]
  have hKsq : K ^ 2 / (4 * eta) ≤ eta / 4 * lam⁻¹ ^ 2 := by
    have h1 : K ^ 2 ≤ (eta / lam) ^ 2 := by nlinarith [hKnn, hKle, hlam]
    have h2 : (eta / lam) ^ 2 = eta ^ 2 * lam⁻¹ ^ 2 := by field_simp
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * eta)]
    nlinarith [h1, h2, heta, sq_nonneg lam⁻¹]
  have hGnn : (0 : ℝ) ≤ G := hG
  calc K * Real.sqrt M * Real.sqrt G
      ≤ eta * (Real.sqrt M * Real.sqrt M) +
          K ^ 2 / (4 * eta) * (Real.sqrt G * Real.sqrt G) := hbase
    _ = eta * M + K ^ 2 / (4 * eta) * G := by rw [hsqM, hsqG]
    _ ≤ eta * M + eta / 4 * lam⁻¹ ^ 2 * G := by
        have := mul_le_mul_of_nonneg_right hKsq hGnn
        linarith [this]
    _ = eta * M + eta / 4 * (lam⁻¹ ^ 2 * G) := by ring

/-- **The final step of the proof of the local `L²` resolvent estimate.**

*The condition of the lemma and Young's inequality give the estimate.* Written out: from the
intermediate display

```
t⁻¹ m + e ≤ C η^{-13/2} (Λ/λ)^{12} √M (λ √M + √G) + (η/2) t⁻¹ M
```

and the smallness condition `t Λ^{12} λ^{-11} ≤ C⁻¹ η^{15/2}` one gets

```
m + t e ≤ 3 η (M + λ^{-2} G) .
```

Here `m`, `e` are the mass and the coefficient energy on the middle third and
`M`, `G` the mass and the squared datum norm on the whole cube, all in the
normalization of the manuscript (`ℓ = 1`; the `ℓ⁴` of the source term is
restored by scaling). -/
theorem localL2_resolvent_of_display
    {t lam Lam eta C m e M G : ℝ}
    (ht : 0 < t) (hlam : 0 < lam) (heta : 0 < eta) (hC : 0 < C)
    (hM : 0 ≤ M) (hG : 0 ≤ G)
    (hcond : t * (Lam ^ 12 * lam⁻¹ ^ 11) ≤ C⁻¹ * eta ^ ((15 : ℝ) / 2))
    (hdisplay : t⁻¹ * m + e ≤
      C * eta ^ (-(13 : ℝ) / 2) * (Lam / lam) ^ 12 * Real.sqrt M *
        (lam * Real.sqrt M + Real.sqrt G) + eta / 2 * (t⁻¹ * M)) :
    m + t * e ≤ 3 * eta * (M + lam⁻¹ ^ 2 * G) := by
  obtain ⟨K, hK_def⟩ : ∃ K : ℝ, K = t * (C * eta ^ (-(13 : ℝ) / 2) * (Lam / lam) ^ 12) :=
    ⟨_, rfl⟩
  have hpow_pos : 0 < eta ^ (-(13 : ℝ) / 2) := Real.rpow_pos_of_pos heta _
  have hKlam : K * lam ≤ eta := by
    have hratio : (Lam / lam) ^ 12 * lam = Lam ^ 12 * lam⁻¹ ^ 11 := by
      field_simp
    have hstep : K * lam =
        C * eta ^ (-(13 : ℝ) / 2) * (t * (Lam ^ 12 * lam⁻¹ ^ 11)) := by
      rw [hK_def, ← hratio]; ring
    have hmul : C * eta ^ (-(13 : ℝ) / 2) * (t * (Lam ^ 12 * lam⁻¹ ^ 11)) ≤
        C * eta ^ (-(13 : ℝ) / 2) * (C⁻¹ * eta ^ ((15 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hcond (by positivity)
    have hcollapse : C * eta ^ (-(13 : ℝ) / 2) * (C⁻¹ * eta ^ ((15 : ℝ) / 2)) = eta := by
      have hCC : C * C⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hC)
      have hetapow : eta ^ (-(13 : ℝ) / 2) * eta ^ ((15 : ℝ) / 2) = eta := by
        rw [← Real.rpow_add heta]
        norm_num
      calc C * eta ^ (-(13 : ℝ) / 2) * (C⁻¹ * eta ^ ((15 : ℝ) / 2))
          = (C * C⁻¹) * (eta ^ (-(13 : ℝ) / 2) * eta ^ ((15 : ℝ) / 2)) := by ring
        _ = eta := by rw [hCC, hetapow]; ring
    rw [hstep]
    exact le_trans hmul (le_of_eq hcollapse)
  have hKnn : 0 ≤ K := by
    rw [hK_def]
    positivity
  have hKle : K ≤ eta / lam := by
    rw [le_div_iff₀ hlam]
    exact hKlam
  have hmul := mul_le_mul_of_nonneg_left hdisplay ht.le
  have hexp : t * (t⁻¹ * m + e) = m + t * e := by field_simp
  have hrhs : t * (C * eta ^ (-(13 : ℝ) / 2) * (Lam / lam) ^ 12 * Real.sqrt M *
        (lam * Real.sqrt M + Real.sqrt G) + eta / 2 * (t⁻¹ * M)) =
      K * Real.sqrt M * (lam * Real.sqrt M + Real.sqrt G) + eta / 2 * M := by
    rw [hK_def]
    field_simp
  rw [hexp, hrhs] at hmul
  have hsqM : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM
  have hmassterm : K * Real.sqrt M * (lam * Real.sqrt M) = (K * lam) * M := by
    calc K * Real.sqrt M * (lam * Real.sqrt M)
        = (K * lam) * (Real.sqrt M * Real.sqrt M) := by ring
      _ = (K * lam) * M := by rw [hsqM]
  have hmass : K * Real.sqrt M * (lam * Real.sqrt M) ≤ eta * M := by
    rw [hmassterm]
    exact mul_le_mul_of_nonneg_right hKlam hM
  have hyoung := localL2_resolvent_young_bound heta hlam hM hG hKnn hKle
  have hdistr : K * Real.sqrt M * (lam * Real.sqrt M + Real.sqrt G) =
      K * Real.sqrt M * (lam * Real.sqrt M) + K * Real.sqrt M * Real.sqrt G := by ring
  have hGterm : (0 : ℝ) ≤ lam⁻¹ ^ 2 * G := by positivity
  have e1 : eta * M + (eta * M + eta / 4 * (lam⁻¹ ^ 2 * G)) + eta / 2 * M ≤
      3 * eta * (M + lam⁻¹ ^ 2 * G) := by
    have hA : (0 : ℝ) ≤ eta * M := mul_nonneg heta.le hM
    have hB : (0 : ℝ) ≤ eta * (lam⁻¹ ^ 2 * G) := mul_nonneg heta.le hGterm
    have hexpand : 3 * eta * (M + lam⁻¹ ^ 2 * G) =
        3 * (eta * M) + 3 * (eta * (lam⁻¹ ^ 2 * G)) := by ring
    have hleft : eta * M + (eta * M + eta / 4 * (lam⁻¹ ^ 2 * G)) + eta / 2 * M =
        (5 / 2) * (eta * M) + (1 / 4) * (eta * (lam⁻¹ ^ 2 * G)) := by ring
    rw [hexpand, hleft]
    linarith [hA, hB]
  linarith only [hmul, hmass, hyoung, hdistr, e1]

/-! ### The coarse-grained contraction, conditional on the two named inputs -/

/-- **The interpolated ("mesoscopic") cutoff-product price.**

The manuscript prices the cross term of the tested identity by Besov duality,
splitting the positive Besov norm of the cutoff product `chi u ∇chi` at a
mesoscopic scale `w = β^{1/(1-s)} ℓ`.  Both halves of that split appear here:
the fluctuation half carries the small factor `β` in front of the energy, the
mean half carries `β⁻¹` in front of `√E √M`.

With `P ≍ C(d) (Λ_{1/16}/λ_{1/16})^{1/2}` and `R ≍ C(d) Λ_{1/16}^{1/2} ℓ⁻¹`
this is what
`SubdiffusiveProcess.Frozen.Section2.coarse_grained_poincare` (both clauses),
`abs_cubeAverage_vecDot_cutoffProduct_le` and
`circNegativeBesovNorm_component_le_paperNegativeBesovVectorNorm`
(`WholeSpaceRowsBesovCutoff.lean`) are supposed to deliver — *once the
positive-Besov factor is split at a mesoscopic depth*.  The proved
whole-cube price is the case `β = 1` and is, by itself, insufficient. -/
def MesoscopicCrossPrice {d : ℕ} (a : Vec d → ℝ) (W : Set (Vec d))
    (w : Vec d → ℝ) (G : Vec d → Vec d) (chi : Vec d → ℝ) (t P R S : ℝ) : Prop :=
  ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
    |2 * ∫ x in W, a x * chi x * w x *
        vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume| ≤
      beta * P * (∫ x in W, a x * vecNormSq (G x) ∂volume) +
        beta⁻¹ * R * Real.sqrt (∫ x in W, a x * vecNormSq (G x) ∂volume) *
          Real.sqrt (∫ x in W, w x ^ 2 ∂volume) +
        beta * S * (t⁻¹ * ∫ x in W, w x ^ 2 ∂volume)

/-- **The coarse energy bound.**  `t ∫_W a|∇u|² ≤ Γ ∫_W u²` with `Γ` a coarse
quantity (`Γ ≍ Λ_{1/16}/λ_{1/16}`).  This is the `L^∞`-free replacement for the
trivial energy identity; the manuscript obtains it by running the coarse
Caccioppoli inequality on mesoscopic descendants of scale `≈ (λ_{1/16} t)^{1/2}`,
the scale at which the Dirichlet `H²` lift of the mass term is efficient. -/
def CoarseEnergyBound {d : ℕ} (a : Vec d → ℝ) (W : Set (Vec d))
    (w : Vec d → ℝ) (G : Vec d → Vec d) (t Gam : ℝ) : Prop :=
  t * ∫ x in W, a x * vecNormSq (G x) ∂volume ≤ Gam * ∫ x in W, w x ^ 2 ∂volume

/-- **The coarse-grained local `L²` contraction, cutoff form.**

The coarse counterpart of `massive_local_l2_contraction_of_cutoff`: the
`L^∞` bound `Lam` of the coefficient is gone, and the contraction factor is the
free parameter `eta`, provided the mesoscopic price and the coarse energy bound
hold and

```
16 P² R² Γ³ t ≤ η⁴ .
```

With `P ≍ (Λ/λ)^{1/2}`, `R ≍ Λ^{1/2} ℓ⁻¹`, `Γ ≍ Λ/λ` this smallness condition
reads `t ℓ⁻² Λ^5 λ^{-4} ≤ c η⁴`, which the manuscript's condition
`t ℓ⁻² Λ_{1/16}^{12} λ_{1/16}^{-11} ≤ C⁻¹ η^{15/2}` implies whenever
`λ_{1/16} ≤ Λ_{1/16}` and `η ≤ 1`. -/
theorem massive_local_l2_coarse_contraction_of_price
    {a : Vec d → ℝ} {lam Lam t eta P R Ssmall Gam K : ℝ} {W S : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (ht : 0 < t) (heta : 0 < eta)
    (hP : 0 < P) (hGam : 0 < Gam) (hR : 0 ≤ R) (hS : 0 ≤ Ssmall)
    (hbeta1 : eta ≤ 3 * (P * Gam + Ssmall))
    (hSW : S ⊆ W) (hSmeas : MeasurableSet S)
    (u : H1Function W)
    (hu : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹ W u (fun _ ↦ (0 : ℝ)))
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi) (hchiS : tsupport chi ⊆ W)
    (hchi_le : ∀ x, |chi x| ≤ 1) (hchi_one : ∀ x ∈ S, chi x = 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K)
    (hprice : MesoscopicCrossPrice a W u.toFun u.grad chi t P R Ssmall)
    (henergy : CoarseEnergyBound a W u.toFun u.grad t Gam)
    (hsmall : 81 * (P * Gam + Ssmall) ^ 2 * R ^ 2 * Gam * t ≤ eta ^ 4) :
    (∫ x in S, u.toFun x ^ 2 ∂volume) +
        t * ∫ x in S, a x * vecNormSq (u.grad x) ∂volume ≤
      eta * ∫ x in W, u.toFun x ^ 2 ∂volume := by
  classical
  have hWmeas : MeasurableSet W := hW.isOpen.measurableSet
  have hMnn : (0 : ℝ) ≤ ∫ x in W, u.toFun x ^ 2 ∂volume :=
    setIntegral_nonneg hWmeas fun x _ ↦ sq_nonneg _
  have hstep : ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
      t⁻¹ * (∫ x in S, u.toFun x ^ 2 ∂volume) +
          ∫ x in S, a x * vecNormSq (u.grad x) ∂volume ≤
        beta * P * (∫ x in W, a x * vecNormSq (u.grad x) ∂volume) +
          beta⁻¹ * R * Real.sqrt (∫ x in W, a x * vecNormSq (u.grad x) ∂volume) *
            Real.sqrt (∫ x in W, u.toFun x ^ 2 ∂volume) +
          beta * Ssmall * (t⁻¹ * ∫ x in W, u.toFun x ^ 2 ∂volume) + 0 := by
    intro beta hbeta hbeta1'
    have hforce : |∫ x in W, (fun _ ↦ (0 : ℝ)) x * chi x ^ 2 * u.toFun x ∂volume| ≤ 0 := by
      simp
    have := massive_cutoff_mass_energy_le_of_cross_bound hW hEll haNonneg ht hSW hSmeas
      u hu hchi hchiC hchiS hchi_le hchi_one hK (hprice beta hbeta hbeta1') hforce
    linarith [this]
  have hmain := mesoscopic_mass_contraction (t := t) (eta := eta) (P := P) (R := R)
    (S := Ssmall) (Gam := Gam) (m := ∫ x in S, u.toFun x ^ 2 ∂volume)
    (e := ∫ x in S, a x * vecNormSq (u.grad x) ∂volume)
    (E := ∫ x in W, a x * vecNormSq (u.grad x) ∂volume)
    (M := ∫ x in W, u.toFun x ^ 2 ∂volume) (D := 0)
    ht heta hP hGam hR hS hMnn hbeta1 hstep henergy hsmall
  linarith [hmain]

open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay in
/-- **The coarse-grained local `L²` resolvent contraction on a centred threefold
enlargement**, i.e. the coarse counterpart of
`localL2_resolvent_translatedCube_contraction`
conditional on exactly two named
inputs: the mesoscopic cutoff-product price (for every cutoff adapted to the
pair `(z + □_n, z + □_{n+1})`) and the coarse energy bound.

No `L^∞` bound on the coefficient appears: `lam` and `Lam` are used only for the
qualitative ellipticity of the datum (`a, a⁻¹ ∈ L^∞(Q)` in the manuscript's
hypotheses), never in the constants. -/
theorem localL2_resolvent_coarse_translatedCube_contraction
    {a : Vec d → ℝ} {lam Lam t eta P R Ssmall Gam : ℝ} {n : ℤ} {z : Vec d}
    (hEll : IsEllipticFieldOn lam Lam (translatedCube d (n + 1) z)
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (ht : 0 < t) (heta : 0 < eta)
    (hP : 0 < P) (hGam : 0 < Gam) (hR : 0 ≤ R) (hS : 0 ≤ Ssmall)
    (hbeta1 : eta ≤ 3 * (P * Gam + Ssmall))
    (u : H1Function (translatedCube d (n + 1) z))
    (hu : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
      (translatedCube d (n + 1) z) u (fun _ ↦ (0 : ℝ)))
    (hprice : ∀ chi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi → (∀ x, |chi x| ≤ 1) →
      (∀ x ∈ translatedCube d n z, chi x = 1) → HasCompactSupport chi →
      tsupport chi ⊆ translatedCube d (n + 1) z →
      (∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤
        translatedCubeCutoffGradBound d n) →
      MesoscopicCrossPrice a (translatedCube d (n + 1) z) u.toFun u.grad chi
        t P R Ssmall)
    (henergy : CoarseEnergyBound a (translatedCube d (n + 1) z) u.toFun u.grad t Gam)
    (hsmall : 81 * (P * Gam + Ssmall) ^ 2 * R ^ 2 * Gam * t ≤ eta ^ 4) :
    (∫ x in translatedCube d n z, u.toFun x ^ 2 ∂volume) +
        t * ∫ x in translatedCube d n z, a x * vecNormSq (u.grad x) ∂volume ≤
      eta * ∫ x in translatedCube d (n + 1) z, u.toFun x ^ 2 ∂volume := by
  classical
  obtain ⟨chi, hchi, hchi_le, hchi_one, hchiC, hchiS, hK⟩ :=
    exists_smooth_translatedCube_cutoff d n z
  exact massive_local_l2_coarse_contraction_of_price
    (isOpenBoundedConvexDomain_translatedCube d (n + 1) z) hEll haNonneg ht heta
    hP hGam hR hS hbeta1 (translatedCube_subset_succ d n z)
    (isOpenBoundedConvexDomain_translatedCube d n z).isOpen.measurableSet u hu
    hchi hchiC hchiS hchi_le hchi_one hK
    (hprice chi hchi hchi_le hchi_one hchiC hchiS hK) henergy hsmall

/-- **The manuscript's smallness condition implies the mesoscopic one.**

For the coarse choices `(P Γ + S)² ≤ c (Λ/λ)³`, `R² ≤ c Λ` and `Γ ≤ c (Λ/λ)`
(in the normalization `ℓ = 1`; recall `P ≍ (Λ/λ)^{1/2}`, `R ≍ Λ^{1/2}`,
`Γ ≍ Λ/λ`, `S ≍ C(d)`), the condition `81 (P Γ + S)² R² Γ t ≤ η⁴` used by
`massive_local_l2_coarse_contraction_of_price` follows from the manuscript's
`t Λ^{12} λ^{-11} ≤ C⁻¹ η⁴` (which its
`t Λ_{1/16}^{12} λ_{1/16}^{-11} ≤ C⁻¹ η^{15/2}`, implies for `η ≤ 1`), because `λ ≤ Λ`
makes the exponent pair `(12,11)` dominate the pair `(5,4)` that the
mesoscopic split needs. -/
theorem mesoscopic_smallness_of_paper_condition
    {t lam Lam eta c P R Ssmall Gam : ℝ} (ht : 0 < t) (hlam : 0 < lam)
    (hlamLam : lam ≤ Lam) (hc : 0 < c) (hGam0 : 0 ≤ Gam)
    (hPS : (P * Gam + Ssmall) ^ 2 ≤ c * (Lam / lam) ^ 3)
    (hR : R ^ 2 ≤ c * Lam) (hGam : Gam ≤ c * (Lam / lam))
    (hcond : t * (Lam ^ 12 * lam⁻¹ ^ 11) ≤ (81 * c ^ 3)⁻¹ * eta ^ 4) :
    81 * (P * Gam + Ssmall) ^ 2 * R ^ 2 * Gam * t ≤ eta ^ 4 := by
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hlamLam
  have hratio : (1 : ℝ) ≤ Lam / lam := (one_le_div hlam).2 hlamLam
  have h1 : (P * Gam + Ssmall) ^ 2 * R ^ 2 ≤ (c * (Lam / lam) ^ 3) * (c * Lam) :=
    mul_le_mul hPS hR (sq_nonneg R) (by positivity)
  have h2 : (P * Gam + Ssmall) ^ 2 * R ^ 2 * Gam ≤
      (c * (Lam / lam) ^ 3) * (c * Lam) * (c * (Lam / lam)) :=
    mul_le_mul h1 hGam hGam0 (by positivity)
  have hcollect : (c * (Lam / lam) ^ 3) * (c * Lam) * (c * (Lam / lam)) =
      c ^ 3 * ((Lam / lam) ^ 4 * Lam) := by ring
  have hdom : (Lam / lam) ^ 4 * Lam ≤ Lam ^ 12 * lam⁻¹ ^ 11 := by
    have hA : (Lam / lam) ^ 4 * Lam = Lam ^ 5 * lam⁻¹ ^ 4 := by field_simp
    have hB : Lam ^ 12 * lam⁻¹ ^ 11 = (Lam ^ 5 * lam⁻¹ ^ 4) * (Lam / lam) ^ 7 := by
      field_simp
    have hC : (1 : ℝ) ≤ (Lam / lam) ^ 7 := one_le_pow₀ hratio
    have hD : (0 : ℝ) ≤ Lam ^ 5 * lam⁻¹ ^ 4 := by positivity
    calc (Lam / lam) ^ 4 * Lam = Lam ^ 5 * lam⁻¹ ^ 4 := hA
      _ ≤ (Lam ^ 5 * lam⁻¹ ^ 4) * (Lam / lam) ^ 7 := by nlinarith [hC, hD]
      _ = Lam ^ 12 * lam⁻¹ ^ 11 := hB.symm
  have hstep : (P * Gam + Ssmall) ^ 2 * R ^ 2 * Gam ≤
      c ^ 3 * (Lam ^ 12 * lam⁻¹ ^ 11) := by
    refine le_trans h2 ?_
    rw [hcollect]
    exact mul_le_mul_of_nonneg_left hdom (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ 81 * t)
  have hfinal : 81 * c ^ 3 * (t * (Lam ^ 12 * lam⁻¹ ^ 11)) ≤ eta ^ 4 := by
    have h81 : (0 : ℝ) < 81 * c ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_left hcond h81.le
    calc 81 * c ^ 3 * (t * (Lam ^ 12 * lam⁻¹ ^ 11))
        ≤ 81 * c ^ 3 * ((81 * c ^ 3)⁻¹ * eta ^ 4) := this
      _ = eta ^ 4 := by field_simp
  calc 81 * (P * Gam + Ssmall) ^ 2 * R ^ 2 * Gam * t
      = 81 * t * ((P * Gam + Ssmall) ^ 2 * R ^ 2 * Gam) := by ring
    _ ≤ 81 * t * (c ^ 3 * (Lam ^ 12 * lam⁻¹ ^ 11)) := hmul
    _ = 81 * c ^ 3 * (t * (Lam ^ 12 * lam⁻¹ ^ 11)) := by ring
    _ ≤ eta ^ 4 := hfinal

/-! ### The carrier-level coarse cell contraction -/

open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay SubdiffusiveProcess.Frozen.Section8 in
/-- **The coarse-grained cell contraction for the frozen carrier.**

The coarse counterpart of `wholeSpaceSolution_cell_mass_contraction`: for a
whole-space divergence-resolvent solution whose datum vanishes on the centred
enlargement `Q̂ = z + □_{n+1}`,

```
∫_Q u² ≤ eta ∫_{Q̂} u²
```

as soon as the mesoscopic price and the coarse energy bound hold on `Q̂` with
`16 P² R² Γ³ t ≤ η⁴`.  No `L^∞` bound on the coefficient is used. -/
theorem wholeSpaceSolution_cell_coarse_mass_contraction
    {a f : Vec d → ℝ} {t lam Lam eta P R Ssmall Gam : ℝ} {n : ℤ} {z : Vec d}
    (ht : 0 < t) (heta : 0 < eta)
    (hEll : IsEllipticFieldOn lam Lam (translatedCube d (n + 1) z)
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x)
    (hP : 0 < P) (hGam : 0 < Gam) (hR : 0 ≤ R) (hS : 0 ≤ Ssmall)
    (hbeta1 : eta ≤ 3 * (P * Gam + Ssmall))
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hf0 : ∀ x ∈ translatedCube d (n + 1) z, f x = 0)
    (hprice : ∀ chi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi → (∀ x, |chi x| ≤ 1) →
      (∀ x ∈ translatedCube d n z, chi x = 1) → HasCompactSupport chi →
      tsupport chi ⊆ translatedCube d (n + 1) z →
      (∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤
        translatedCubeCutoffGradBound d n) →
      MesoscopicCrossPrice a (translatedCube d (n + 1) z) u.toFun u.grad chi
        t P R Ssmall)
    (henergy : CoarseEnergyBound a (translatedCube d (n + 1) z)
      u.toFun u.grad t Gam)
    (hsmall : 81 * (P * Gam + Ssmall) ^ 2 * R ^ 2 * Gam * t ≤ eta ^ 4) :
    ∫ x in translatedCube d n z, u.toFun x ^ 2 ∂volume ≤
      eta * ∫ x in translatedCube d (n + 1) z, u.toFun x ^ 2 ∂volume := by
  classical
  set W : Set (Vec d) := translatedCube d (n + 1) z with hW_def
  set Q : Set (Vec d) := translatedCube d n z with hQ_def
  have hWdom : IsOpenBoundedConvexDomain W :=
    isOpenBoundedConvexDomain_translatedCube d (n + 1) z
  have hQdom : IsOpenBoundedConvexDomain Q :=
    isOpenBoundedConvexDomain_translatedCube d n z
  have hWmeas : MeasurableSet W := hWdom.isOpen.measurableSet
  have hQmeas : MeasurableSet Q := hQdom.isOpen.measurableSet
  have hQW : Q ⊆ W := translatedCube_subset_succ d n z
  obtain ⟨v, hval, hgrad, hsol⟩ := u.locally_weak_solution W hWdom
  have hsol0 : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹ W v
      (fun _ ↦ (0 : ℝ)) := by
    intro phi
    refine (hsol phi).trans ?_
    refine setIntegral_congr_fun hWmeas fun x hx ↦ ?_
    simp [hf0 x hx]
  -- transport the integrals between the local representative and the carrier
  have hWval : ∫ x in W, v.toFun x ^ 2 ∂volume = ∫ x in W, u.toFun x ^ 2 ∂volume := by
    refine setIntegral_congr_fun hWmeas fun x hx ↦ ?_
    rw [hval x hx]
  have hQval : ∫ x in Q, v.toFun x ^ 2 ∂volume = ∫ x in Q, u.toFun x ^ 2 ∂volume := by
    refine setIntegral_congr_fun hQmeas fun x hx ↦ ?_
    rw [hval x (hQW hx)]
  have hWen : ∫ x in W, a x * vecNormSq (v.grad x) ∂volume =
      ∫ x in W, a x * vecNormSq (u.grad x) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hgrad] with x hx
    rw [hx]
  have hWcross : ∀ chi : Vec d → ℝ,
      ∫ x in W, a x * chi x * v.toFun x *
          vecDot (v.grad x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume =
        ∫ x in W, a x * chi x * u.toFun x *
          vecDot (u.grad x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume := by
    intro chi
    refine integral_congr_ae ?_
    filter_upwards [hgrad, ae_restrict_mem hWmeas] with x hx hxW
    rw [hx, hval x hxW]
  have hpriceV : ∀ chi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi → (∀ x, |chi x| ≤ 1) →
      (∀ x ∈ Q, chi x = 1) → HasCompactSupport chi → tsupport chi ⊆ W →
      (∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤
        translatedCubeCutoffGradBound d n) →
      MesoscopicCrossPrice a W v.toFun v.grad chi t P R Ssmall := by
    intro chi h1 h2 h3 h4 h5 h6 beta hb1 hb2
    have := hprice chi h1 h2 h3 h4 h5 h6 beta hb1 hb2
    rw [hWcross chi, hWen, hWval]
    exact this
  have henergyV : CoarseEnergyBound a W v.toFun v.grad t Gam := by
    unfold CoarseEnergyBound
    rw [hWen, hWval]
    exact henergy
  have hbase := localL2_resolvent_coarse_translatedCube_contraction hEll haNonneg
    ht heta hP hGam hR hS hbeta1 v hsol0 hpriceV henergyV hsmall
  have hQen : 0 ≤ t * ∫ x in Q, a x * vecNormSq (v.grad x) ∂volume := by
    refine mul_nonneg ht.le (setIntegral_nonneg hQmeas fun x _ ↦ ?_)
    exact mul_nonneg (haNonneg x) (vecNormSq_nonneg _)
  rw [hQval, hWval] at hbase
  linarith [hbase, hQen]

/-! ### The exterior decay from per-cell contractions -/

open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay SubdiffusiveProcess.Frozen.Section8 in
/-- **The exterior row from per-cell mass contractions.**

The analytic input of `wholeSpaceSolution_exterior_decay_of_stopping_cells` is
isolated: instead of the `L^∞` smallness condition
`4096 d Lam t (3^{scale})⁻² ≤ theta0` together with the pointwise coefficient
bound on the enlargement, only the per-cell mass contraction

```
∫_Q u² ≤ theta0 ∫_{Q̂} u²
```

is assumed.  Both the `L^∞` route (`wholeSpaceSolution_cell_mass_contraction`) and the coarse-grained route
(`wholeSpaceSolution_cell_coarse_mass_contraction` above) supply exactly this,
so the stopping partition can consume either without change. -/
theorem wholeSpaceSolution_exterior_decay_of_cell_mass_contractions
    {a f : Vec d → ℝ} {t : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    {count : ℕ → ℕ}
    (scale : (j : ℕ) → Fin (count j) → ℤ)
    (centre : (j : ℕ) → Fin (count j) → Vec d)
    (exterior : Set (Vec d)) {A theta0 : ℝ} (N D Nnbr : ℕ) {rate : ℝ}
    (hA : 0 ≤ A) (htheta0 : 0 < theta0) (hNnbr : 0 < Nnbr) (hD : 0 < D)
    (heffective : (D : ℝ) * ((Nnbr : ℝ) * theta0) < 1)
    (hsource : ∀ i : Fin (count 0),
      ∫ x in stoppingCell scale centre 0 i, u.toFun x ^ 2 ∂volume ≤ A)
    (hcell : ∀ (j : ℕ) (i : Fin (count j)), 0 < j →
      ∫ x in stoppingCell scale centre j i, u.toFun x ^ 2 ∂volume ≤
        theta0 * ∫ x in stoppingCellEnlargement scale centre j i,
          u.toFun x ^ 2 ∂volume)
    (hnbr : ∀ (j : ℕ) (i : Fin (count j)), 0 < j →
      ∃ s : Finset (Σ k : ℕ, Fin (count k)), s.Nonempty ∧ s.card ≤ Nnbr ∧
        (∀ p ∈ s, j ≤ p.1 + 1) ∧
        stoppingCellEnlargement scale centre j i ⊆
          ⋃ p ∈ s, stoppingCell scale centre p.1 p.2)
    (hcard : ∀ j, count j ≤ N * D ^ j)
    (hcover : exterior ⊆
      ⋃ p : Σ k : ℕ, Fin (count (⌈rate⌉₊ + k)),
        stoppingCell scale centre (⌈rate⌉₊ + p.1) p.2) :
    ∫ x in exterior, u.toFun x ^ 2 ∂volume ≤
      (N : ℝ) * A * (1 - (D : ℝ) * ((Nnbr : ℝ) * theta0))⁻¹ *
        Real.exp (Real.log ((D : ℝ) * ((Nnbr : ℝ) * theta0)) * rate) := by
  classical
  refine integral_sq_exterior_le_of_graph_cells u.toFun u.memL2_toFun count
    (fun j i ↦ stoppingCell scale centre j i) exterior N D hA
    (by positivity) hD heffective hsource ?_ hcard hcover
  intro j i hj
  obtain ⟨s, hsne, hscard, hslevel, hscover⟩ := hnbr j i hj
  obtain ⟨p, hp, hcov⟩ :=
    exists_mem_integral_sq_le_card_mul_of_finset_cover u.memL2_toFun s hsne
      (fun p ↦ stoppingCell scale centre p.1 p.2) hscover
  refine ⟨p, hslevel p hp, ?_⟩
  have hnn : 0 ≤ ∫ x in stoppingCell scale centre p.1 p.2,
      u.toFun x ^ 2 ∂volume :=
    setIntegral_nonneg
      (isOpenBoundedConvexDomain_translatedCube d (scale p.1 p.2)
        (centre p.1 p.2)).isOpen.measurableSet fun x _ ↦ sq_nonneg _
  have hstep : ∫ x in stoppingCell scale centre j i, u.toFun x ^ 2 ∂volume ≤
      theta0 * ((s.card : ℝ) * ∫ x in stoppingCell scale centre p.1 p.2,
        u.toFun x ^ 2 ∂volume) :=
    le_trans (hcell j i hj) (mul_le_mul_of_nonneg_left hcov htheta0.le)
  have hcardR : (s.card : ℝ) ≤ (Nnbr : ℝ) := by exact_mod_cast hscard
  have hle : (s.card : ℝ) * theta0 ≤ (Nnbr : ℝ) * theta0 :=
    mul_le_mul_of_nonneg_right hcardR htheta0.le
  calc ∫ x in stoppingCell scale centre j i, u.toFun x ^ 2 ∂volume
      ≤ theta0 * ((s.card : ℝ) * ∫ x in stoppingCell scale centre p.1 p.2,
          u.toFun x ^ 2 ∂volume) := hstep
    _ = (s.card : ℝ) * theta0 * ∫ x in stoppingCell scale centre p.1 p.2,
          u.toFun x ^ 2 ∂volume := by ring
    _ ≤ (Nnbr : ℝ) * theta0 * ∫ x in stoppingCell scale centre p.1 p.2,
          u.toFun x ^ 2 ∂volume := mul_le_mul_of_nonneg_right hle hnn

/-! ### Why the mesoscopic parameter cannot be dispensed with -/

/-- **The whole-cube price is insufficient, and this is not a matter of
constants.**

If the cross term is priced only at the endpoint `β = 1` — which is what the
proved whole-cube pairing
`abs_cubeAverage_vecDot_cutoffProduct_le` composed with both clauses of
`SubdiffusiveProcess.Frozen.Section2.coarse_grained_poincare` produces, with `P ≍ (Λ/λ)^{1/2}`
— then **no** contraction factor below `P Γ` follows, however small `t` is:
the energy is itself of order `t⁻¹` times the mass, so a price of the form
`P · E` contributes `P Γ` times the mass and nothing in the hypotheses can
make that small.

This is the precise sense in which the manuscript's *"optimized in the
mesoscopic scale"* is not decoration: the price must be sub-quadratic in the
energy (`β E + β⁻¹ √E √M` with `β` free), and it is the mesoscopic splitting of
the positive Besov norm of the cutoff product that produces the free `β`. -/
theorem whole_cube_price_insufficient {t eta P Gam : ℝ}
    (ht : 0 < t) (hP : 0 < P) (hGam : 0 < Gam) (heta : eta < P * Gam) :
    ∃ m e E M : ℝ, 0 ≤ m ∧ 0 ≤ e ∧ 0 ≤ E ∧ 0 ≤ M ∧
      t⁻¹ * m + e ≤ 1 * P * E + 1⁻¹ * 0 * Real.sqrt E * Real.sqrt M +
          1 * 0 * (t⁻¹ * M) ∧
      t * E ≤ Gam * M ∧ ¬(m + t * e ≤ eta * M) := by
  refine ⟨P * Gam, 0, Gam / t, 1, by positivity, le_rfl, by positivity, by norm_num,
    ?_, ?_, ?_⟩
  · have : t⁻¹ * (P * Gam) = 1 * P * (Gam / t) := by field_simp
    rw [this]
    simp
  · rw [mul_div_cancel₀ Gam (ne_of_gt ht)]
    simp
  · simp only [mul_zero, add_zero, mul_one]
    exact not_le.mpr heta

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
