module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumUniqueness
public import Homogenization.Sobolev.Foundations.DifferenceQuotientH1
public import Homogenization.Sobolev.Foundations.Cutoff.Box
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Transport

@[expose] public section

/-!
# The local Caccioppoli estimate for the weighted massive equation

 writes the resolvent equation of
Section 8 as

  `μ ρ u − ∇·(c ∇u) = ρ f`   weakly on `W`,

which is `IsMassiveWeakSolutionOn`.  This file proves the *interior* energy
estimate for that equation: testing against `χ² u` with a smooth cutoff `χ`
and absorbing the cross term by Young's inequality gives

  `∫_W c χ² |∇u|² ≤ 4 ∫_W c u² |∇χ|² + ∫_W ρ f² + ∫_W ρ u²`.

The mass term `μ ∫ ρ χ² u²` is *dropped* on the correct side: it is
nonnegative, so the estimate holds with no lower bound on `μ` beyond `μ ≥ 0`
and with no constant depending on `μ`.

Specialised to the centred cube exhaustion with the smooth box cutoff of
`Homogenization.exists_smoothBoxCutoff` (equal to `1` on `cube d k`, supported
in `cube d (k+1)`), this bounds the energy of *any* solution on the larger cube
by its sup-norm and the forcing — with no reference to the boundary values.
That is what the compact-support exhaustion could not supply: the proved
`exists_uniform_local_gradient_norm_bound` bounds the energy of the *Dirichlet*
solutions by `∫ ρ f²` over the whole large cube, which is finite only when `f`
has compact support.

## Main declarations

* `massive_caccioppoli_cutoff` — the cutoff estimate above.
* `exists_smooth_cube_cutoff` — the smooth cutoff `1` on `cube d k`, supported
  in `cube d (k+1)`, with an explicit squared-gradient bound.
* `massive_cube_energy_le` — the estimate on nested exhaustion cubes, with all
  constants read off `MassiveCubeBounds`.
* `exists_uniform_cube_gradient_bound` — the resulting uniform bound on the
  Hilbert `L²` gradient norm of the restriction to the inner cube, valid for
  every solution on the outer cube with a common sup bound.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-! ### The cutoff estimate -/

/-- The support of a square is the support of the function. -/
private theorem support_sq_eq' {g : Vec d → ℝ} :
    Function.support (fun x ↦ g x ^ 2) = Function.support g := by
  ext x
  simp [Function.mem_support]

/-- The differential of a square, evaluated on a coordinate direction. -/
private theorem fderiv_sq_apply' {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Vec d) (i : Fin d) :
    (fderiv ℝ (fun y ↦ g y ^ 2) x) (basisVec i) =
      2 * g x * (fderiv ℝ g x) (basisVec i) := by
  have hdiff : DifferentiableAt ℝ g x :=
    hg.differentiable (by simp) x
  have h := (hdiff.hasFDerivAt).pow 2
  rw [h.fderiv]
  simp [mul_comm, mul_assoc]

/-! ### Integrability of the two localized energy densities -/

/-- The cutoff energy density `c g² |∇u|²` is integrable when `|g| ≤ 1`. -/
theorem integrableOn_cutoff_energy {c : Vec d → ℝ} {lam Lam : ℝ} {W : Set (Vec d)}
    (hWmeas : MeasurableSet W)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (u : H1Function W) {g : Vec d → ℝ}
    (hgmeas : AEStronglyMeasurable g (volume.restrict W))
    (hg : ∀ x, |g x| ≤ 1) :
    IntegrableOn (fun x ↦ c x * g x ^ 2 * vecNormSq (u.grad x)) W := by
  have hF : MemVectorL2 W (fun x ↦ g x • u.grad x) := by
    refine MemLp.mono u.grad_memVectorL2
      (hgmeas.smul u.grad_memVectorL2.aestronglyMeasurable) ?_
    filter_upwards with x
    rw [norm_smul, Real.norm_eq_abs]
    calc |g x| * ‖u.grad x‖ ≤ 1 * ‖u.grad x‖ :=
          mul_le_mul_of_nonneg_right (hg x) (norm_nonneg _)
      _ = ‖u.grad x‖ := one_mul _
  have hbase := integrableOn_energy_term hEll hF hF
  refine hbase.congr_fun (fun x _ ↦ ?_) hWmeas
  simp [vecDot, vecNormSq, Finset.mul_sum]
  ring_nf

/-- The density `c u² |G|²` of the Caccioppoli right-hand side is integrable
when the vector field `G` is continuous with bounded squared norm. -/
theorem integrableOn_value_gradSq {c : Vec d → ℝ} {lam Lam K : ℝ} {W : Set (Vec d)}
    (hWmeas : MeasurableSet W)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (u : H1Function W) {G : Vec d → Vec d} (hG : Continuous G)
    (hK : ∀ x, vecNormSq (G x) ≤ K) :
    IntegrableOn (fun x ↦ c x * u.toFun x ^ 2 * vecNormSq (G x)) W := by
  have hK0 : (0 : ℝ) ≤ K := le_trans (vecNormSq_nonneg _) (hK 0)
  have hnorm : ∀ x, ‖G x‖ ≤ Real.sqrt K := by
    intro x
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg K)).mpr fun i ↦ ?_
    have h1 : G x i ^ (2 : ℕ) ≤ K :=
      le_trans (sq_apply_le_vecNormSq (G x) i) (hK x)
    calc ‖G x i‖ = Real.sqrt (G x i ^ (2 : ℕ)) := by
          rw [Real.sqrt_sq_eq_abs]; rfl
      _ ≤ Real.sqrt K := Real.sqrt_le_sqrt h1
  have hF : MemVectorL2 W (fun x ↦ u.toFun x • G x) := by
    refine MemLp.mono (u.memL2.const_mul (Real.sqrt K)) ?_ ?_
    · exact u.memL2.aestronglyMeasurable.smul hG.aestronglyMeasurable
    · filter_upwards with x
      have hle : ‖u.toFun x • G x‖ = |u.toFun x| * ‖G x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      rw [hle]
      have hstep : |u.toFun x| * ‖G x‖ ≤ |u.toFun x| * Real.sqrt K :=
        mul_le_mul_of_nonneg_left (hnorm x) (abs_nonneg _)
      refine hstep.trans ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg K)]
      exact le_of_eq (mul_comm _ _)
  have hbase := integrableOn_energy_term hEll hF hF
  refine hbase.congr_fun (fun x _ ↦ ?_) hWmeas
  simp [vecDot, vecNormSq, Finset.mul_sum]
  ring_nf

/-- **The local Caccioppoli estimate for the weighted massive equation.**

If `u` solves `μ ρ u − ∇·(c ∇u) = ρ f` weakly on a bounded open convex domain
`W` and `χ` is a smooth cutoff with `|χ| ≤ 1` compactly supported in `W`, then

```
∫_W c χ² |∇u|² ≤ 4 ∫_W c u² |∇χ|² + ∫_W ρ f² + ∫_W ρ u² .
```

Only nonnegativity of `c`, `ρ` and `μ` is used; ellipticity enters solely to
know that the energy pairings are integrable.

-/
theorem massive_caccioppoli_cutoff
    {c rho : Vec d → ℝ} {mu lam Lam rhoMax K : ℝ} {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hcNonneg : ∀ x, 0 ≤ c x) (hmu : 0 ≤ mu)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    (hrhoNonneg : ∀ x ∈ W, 0 ≤ rho x)
    (u : H1Function W) {f : Vec d → ℝ} (hf : MemL2On W f)
    (hu : IsMassiveWeakSolutionOn c rho mu W u f)
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi) (hchiS : tsupport chi ⊆ W)
    (hchi_le : ∀ x, |chi x| ≤ 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K) :
    ∫ x in W, c x * chi x ^ 2 * vecNormSq (u.grad x) ∂volume ≤
      4 * ∫ x in W, c x * u.toFun x ^ 2 *
            vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume +
        ((∫ x in W, rho x * f x * f x ∂volume) +
          ∫ x in W, rho x * u.toFun x * u.toFun x ∂volume) := by
  classical
  have hWmeas : MeasurableSet W := hW.isOpen.measurableSet
  set gchi : Vec d → Vec d := fun x i ↦ (fderiv ℝ chi x) (basisVec i) with hgchi_def
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
    exact le_of_eq (support_sq_eq' (g := chi))
  set phi : H10Function W :=
    u.mulContDiffHasCompactSupportToH10 hW heta hetaC hetaS with hphi_def
  have hphi_toFun : phi.toH1Function.toFun = fun x ↦ eta x * u.toFun x :=
    H1Function.mulContDiffHasCompactSupportToH10_toFun u hW heta hetaC hetaS
  set psi : H1Function W := u.mulContDiffHasCompactSupport heta hetaC with hpsi_def
  have hpsi_grad : psi.grad =
      fun x i ↦ eta x * u.grad x i + u.toFun x * (fderiv ℝ eta x) (basisVec i) := by
    simp [hpsi_def]
  have hgrad : phi.toH1Function.grad =ᵐ[volume.restrict W] psi.grad := by
    refine Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq hW.isOpen ?_
    filter_upwards with x
    rw [hphi_toFun]
    simp [hpsi_def]
  -- continuity and boundedness of the cutoff gradient
  have hgchi_cont : Continuous gchi := by
    refine continuous_pi fun i ↦ ?_
    exact ((hchi.continuous_fderiv (by simp)).clm_apply
      continuous_const)
  have hint_cut : IntegrableOn
      (fun x ↦ c x * u.toFun x ^ 2 * vecNormSq (gchi x)) W :=
    integrableOn_value_gradSq hWmeas hEll u hgchi_cont hK
  have hint_chi : IntegrableOn
      (fun x ↦ c x * chi x ^ 2 * vecNormSq (u.grad x)) W :=
    integrableOn_cutoff_energy hWmeas hEll u
      hchi.continuous.aestronglyMeasurable hchi_le
  have hint_energy : IntegrableOn
      (fun x ↦ vecDot (c x • u.grad x) (psi.grad x)) W :=
    integrableOn_energy_term hEll u.grad_memVectorL2 psi.grad_memVectorL2
  -- the pointwise Young inequality
  have hptwise : ∀ x,
      c x * chi x ^ 2 * vecNormSq (u.grad x) / 2 -
          2 * (c x * u.toFun x ^ 2 * vecNormSq (gchi x)) ≤
        vecDot (c x • u.grad x) (psi.grad x) := by
    intro x
    have hd : psi.grad x =
        fun i ↦ chi x ^ 2 * u.grad x i + u.toFun x * (2 * chi x * gchi x i) := by
      rw [hpsi_grad]
      funext i
      simp only [heta_def, hgchi_def, fderiv_sq_apply' hchi x i]
    have hexp : vecDot (c x • u.grad x) (psi.grad x) =
        c x * (chi x ^ 2 * vecNormSq (u.grad x) +
          2 * chi x * u.toFun x * vecDot (u.grad x) (gchi x)) := by
      rw [hd]
      simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul, mul_add,
        Finset.sum_add_distrib, Finset.mul_sum]
      ring_nf
      congr 1 <;> exact Finset.sum_congr rfl fun i _ ↦ by ring
    have hyoung := abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
      (chi x) (2 * u.toFun x) (u.grad x) (gchi x)
    have hyoung' : -(chi x ^ 2 * vecNormSq (u.grad x) / 2 +
          (2 * u.toFun x) ^ 2 * vecNormSq (gchi x) / 2) ≤
        chi x * (2 * u.toFun x) * vecDot (u.grad x) (gchi x) :=
      neg_le_of_abs_le hyoung
    have hGnn := vecNormSq_nonneg (u.grad x)
    have hgnn := vecNormSq_nonneg (gchi x)
    have hax := hcNonneg x
    rw [hexp]
    nlinarith [mul_nonneg hax (mul_nonneg (sq_nonneg (chi x)) hGnn),
      mul_nonneg hax hgnn, hyoung']
  -- the lower bound for the energy integral
  have hminInt : IntegrableOn
      (fun x ↦ c x * chi x ^ 2 * vecNormSq (u.grad x) / 2 -
        2 * (c x * u.toFun x ^ 2 * vecNormSq (gchi x))) W :=
    (hint_chi.div_const 2).sub (hint_cut.const_mul 2)
  have hmono :
      (∫ x in W, (c x * chi x ^ 2 * vecNormSq (u.grad x) / 2 -
          2 * (c x * u.toFun x ^ 2 * vecNormSq (gchi x))) ∂volume) ≤
        ∫ x in W, vecDot (c x • u.grad x) (psi.grad x) ∂volume :=
    integral_mono hminInt.integrable hint_energy.integrable hptwise
  have hminEq :
      (∫ x in W, (c x * chi x ^ 2 * vecNormSq (u.grad x) / 2 -
          2 * (c x * u.toFun x ^ 2 * vecNormSq (gchi x))) ∂volume) =
        (∫ x in W, c x * chi x ^ 2 * vecNormSq (u.grad x) ∂volume) / 2 -
          2 * ∫ x in W, c x * u.toFun x ^ 2 * vecNormSq (gchi x) ∂volume := by
    rw [integral_sub (hint_chi.div_const 2) (hint_cut.const_mul 2),
      integral_div, integral_const_mul]
  -- the weak equation, with the mass term dropped and the forcing term absorbed
  have heq := hu phi
  rw [hphi_toFun] at heq
  have hmassNonneg : 0 ≤
      ∫ x in W, rho x * u.toFun x * (eta x * u.toFun x) ∂volume := by
    refine setIntegral_nonneg hWmeas fun x hx ↦ ?_
    have hr := hrhoNonneg x hx
    have : 0 ≤ rho x * (chi x ^ 2 * (u.toFun x * u.toFun x)) :=
      mul_nonneg hr (mul_nonneg (sq_nonneg _) (mul_self_nonneg _))
    simp only [heta_def]
    nlinarith [this]
  have hforcingInt : IntegrableOn
      (fun x ↦ rho x * f x * (eta x * u.toFun x)) W :=
    integrableOn_mass_term hrhoMeas hrhoBdd hf psi.memL2
  have hforcingBdInt : IntegrableOn
      (fun x ↦ rho x * f x * f x / 2 + rho x * u.toFun x * u.toFun x / 2) W :=
    ((integrableOn_mass_term hrhoMeas hrhoBdd hf hf).div_const 2).add
      ((integrableOn_mass_term hrhoMeas hrhoBdd u.memL2 u.memL2).div_const 2)
  have hforcing :
      (∫ x in W, rho x * f x * (eta x * u.toFun x) ∂volume) ≤
        (∫ x in W, rho x * f x * f x ∂volume) / 2 +
          (∫ x in W, rho x * u.toFun x * u.toFun x ∂volume) / 2 := by
    have hstep : (∫ x in W, rho x * f x * (eta x * u.toFun x) ∂volume) ≤
        ∫ x in W, (rho x * f x * f x / 2 +
          rho x * u.toFun x * u.toFun x / 2) ∂volume := by
      refine setIntegral_mono_on hforcingInt.integrable hforcingBdInt.integrable
        hWmeas fun x hx ↦ ?_
      have hr := hrhoNonneg x hx
      have ht0 : 0 ≤ eta x := by simp only [heta_def]; positivity
      have ht1 : eta x ≤ 1 := by
        simp only [heta_def]
        nlinarith [hchi_le x, abs_nonneg (chi x), sq_abs (chi x)]
      have hcore : f x * (eta x * u.toFun x) ≤
          f x * f x / 2 + u.toFun x * u.toFun x / 2 := by
        nlinarith [sq_nonneg (f x - u.toFun x), sq_nonneg (f x + u.toFun x),
          ht0, ht1]
      calc rho x * f x * (eta x * u.toFun x)
          = rho x * (f x * (eta x * u.toFun x)) := by ring
        _ ≤ rho x * (f x * f x / 2 + u.toFun x * u.toFun x / 2) :=
            mul_le_mul_of_nonneg_left hcore hr
        _ = rho x * f x * f x / 2 + rho x * u.toFun x * u.toFun x / 2 := by ring
    refine hstep.trans (le_of_eq ?_)
    rw [integral_add ((integrableOn_mass_term hrhoMeas hrhoBdd hf hf).div_const 2)
      ((integrableOn_mass_term hrhoMeas hrhoBdd u.memL2 u.memL2).div_const 2),
      integral_div, integral_div]
  -- the energy integral in the equation is the one estimated above
  have henergy_eq : ∫ x in W, vecDot (c x • u.grad x) (phi.toH1Function.grad x) ∂volume =
      ∫ x in W, vecDot (c x • u.grad x) (psi.grad x) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hgrad] with x hx
    rw [hx]
  rw [henergy_eq] at heq
  have hmassmu : 0 ≤ mu * ∫ x in W, rho x * u.toFun x * (eta x * u.toFun x) ∂volume :=
    mul_nonneg hmu hmassNonneg
  rw [hminEq] at hmono
  linarith

/-! ### The smooth cutoff between two consecutive exhaustion cubes -/

/-- The explicit squared-gradient bound of the smooth cutoff which is `1` on
`cube d k` and vanishes off `cube d (k+1)`. -/
def cubeCutoffGradBound (d k : ℕ) : ℝ := (d : ℝ) * (16 / ((1 / 2 : ℝ) * 3 ^ k)) ^ 2

theorem cubeCutoffGradBound_nonneg (d k : ℕ) : 0 ≤ cubeCutoffGradBound d k := by
  unfold cubeCutoffGradBound
  positivity

/-- **A smooth cutoff adapted to two consecutive exhaustion cubes.**  It equals
`1` on `cube d k`, is supported in `cube d (k+1)`, takes values in `[0,1]` and
has squared gradient at most `cubeCutoffGradBound d k`.  Built from
`Homogenization.exists_smoothBoxCutoff` for the box of half-side `3ᵏ/2` with
margin `3ᵏ/2`. -/
theorem exists_smooth_cube_cutoff (d k : ℕ) :
    ∃ chi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ (∀ x, |chi x| ≤ 1) ∧
      (∀ x ∈ cube d (k : ℤ), chi x = 1) ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ cube d ((k + 1 : ℕ) : ℤ) ∧
      ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤
        cubeCutoffGradBound d k := by
  classical
  set r : ℝ := (1 / 2 : ℝ) * 3 ^ k with hr_def
  have hr : 0 < r := by rw [hr_def]; positivity
  have hle : (fun _ : Fin d ↦ -r) ≤ (fun _ : Fin d ↦ r) := by
    intro i
    linarith
  obtain ⟨eta, hsmooth, hIcc, hone, hzero, _hderiv, hsq, _hvol⟩ :=
    exists_smoothBoxCutoff (fun _ : Fin d ↦ -r) (fun _ : Fin d ↦ r) r hr hle
  have hpow : (3 : ℝ) ^ ((k : ℤ)) = (3 : ℝ) ^ k := zpow_natCast 3 k
  have hpow' : (3 : ℝ) ^ (((k + 1 : ℕ) : ℤ)) = (3 : ℝ) ^ (k + 1) := zpow_natCast 3 (k + 1)
  have hpow3 : (3 : ℝ) ^ (k + 1) = 3 * 3 ^ k := by ring
  have h3k : (0 : ℝ) < 3 ^ k := by positivity
  refine ⟨eta, hsmooth, fun x ↦ ?_, fun x hx ↦ ?_, ?_, ?_, fun x ↦ ?_⟩
  · exact abs_le.2 ⟨by linarith [(hIcc x).1], (hIcc x).2⟩
  · refine hone x ?_
    rw [cube, mem_openCubeSet_originCube_iff] at hx
    refine Set.mem_Icc.2 ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · have := (hx i).1
      rw [hpow] at this
      simp only [hr_def]
      linarith
    · have := (hx i).2
      rw [hpow] at this
      simp only [hr_def]
      linarith
  · refine HasCompactSupport.intro (K := Set.Icc (fun _ : Fin d ↦ -r - r)
      (fun _ : Fin d ↦ r + r)) isCompact_Icc fun x hx ↦ hzero x hx
  · refine le_trans (closure_mono (Function.support_subset_iff'.2 fun x hx ↦ hzero x hx)) ?_
    rw [IsClosed.closure_eq isClosed_Icc]
    intro x hx
    rw [Set.mem_Icc] at hx
    rw [cube, mem_openCubeSet_originCube_iff]
    intro i
    have h1 := hx.1 i
    have h2 := hx.2 i
    rw [hpow', hpow3]
    simp only [hr_def] at h1 h2
    constructor <;> linarith
  · have hbound := hsq x
    have hcalc : vecNormSq (fun i ↦ (fderiv ℝ eta x) (basisVec i)) =
        ∑ i, ((fderiv ℝ eta x) (Pi.single i 1)) ^ 2 := by
      simp [vecNormSq, vecDot, basisVec, pow_two]
    rw [hcalc]
    exact le_trans hbound (le_of_eq (by rw [cubeCutoffGradBound, hr_def]))

/-! ### Global positivity of the coefficients from the local cube bounds -/

/-- Every point lies in one exhaustion cube, so the local lower bounds of
`MassiveCubeBounds` give global nonnegativity of the coefficient. -/
theorem MassiveCubeBounds.coeff_nonneg {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (x : Vec d) : 0 ≤ c x := by
  obtain ⟨n, hn⟩ := exists_nat_cube_superset (Bornology.isBounded_singleton (x := x))
  exact le_trans (B.lam_pos n).le (B.coeff_lower n x (hn rfl))

/-- Global nonnegativity of the weight. -/
theorem MassiveCubeBounds.weight_nonneg {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (x : Vec d) : 0 ≤ rho x := by
  obtain ⟨n, hn⟩ := exists_nat_cube_superset (Bornology.isBounded_singleton (x := x))
  exact le_trans (B.rhoMin_pos n).le (B.rho_lower n x (hn rfl))

/-- The upper ellipticity bound of `MassiveCubeBounds`, read off the diagonal of
the scalar coefficient matrix. -/
theorem MassiveCubeBounds.coeff_le [NeZero d] {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (n : ℕ) {x : Vec d} (hx : x ∈ cube d (n : ℤ)) :
    c x ≤ B.Lam n := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  set i : Fin d := ⟨0, hd⟩ with hi
  have habs := abs_apply_le_of_isEllipticFieldOn (B.ell n) hx i i
  have hentry : scalarCoeffField c x i i = c x := by
    simp [scalarCoeffField, Homogenization.scalarMatrix, Matrix.one_apply_eq]
  rw [hentry] at habs
  exact le_trans (le_abs_self _) habs

/-! ### The estimate on nested domains -/

/-- **The Caccioppoli estimate on nested domains, with the right-hand side in
closed form.**  A solution of the massive equation on `W` with an
almost-everywhere sup bound `M` has energy on any subset `Q` where the cutoff
equals `1` bounded by `M`, the forcing, and the local ellipticity and weight
bounds on `W` — with no reference whatsoever to the boundary values of the
solution. -/
theorem massive_energy_le_of_cutoff
    {c rho : Vec d → ℝ} {mu lam Lam rhoMax cMax M K : ℝ} {W Q : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W) (hQmeas : MeasurableSet Q) (hQW : Q ⊆ W)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hcNonneg : ∀ x, 0 ≤ c x) (hcLe : ∀ x ∈ W, c x ≤ cMax) (hmu : 0 ≤ mu)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    (hrhoNonneg : ∀ x ∈ W, 0 ≤ rho x)
    (u : H1Function W) {f : Vec d → ℝ} (hf : MemL2On W f)
    (hu : IsMassiveWeakSolutionOn c rho mu W u f)
    (hM : ∀ᵐ x ∂(volume.restrict W), |u.toFun x| ≤ M)
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi) (hchiS : tsupport chi ⊆ W)
    (hchi_le : ∀ x, |chi x| ≤ 1) (hchi_one : ∀ x ∈ Q, chi x = 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K) :
    ∫ x in Q, c x * vecNormSq (u.grad x) ∂volume ≤
      (4 * K * cMax + rhoMax) * M ^ 2 * (volume W).toReal +
        ∫ x in W, rho x * f x * f x ∂volume := by
  classical
  have hWmeas : MeasurableSet W := hW.isOpen.measurableSet
  have : IsFiniteMeasure (volume.restrict W) :=
    hW.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hK0 : (0 : ℝ) ≤ K := le_trans (vecNormSq_nonneg _) (hK 0)
  have hgchi_cont : Continuous (fun x i ↦ (fderiv ℝ chi x) (basisVec i)) := by
    refine continuous_pi fun i ↦ ?_
    exact ((hchi.continuous_fderiv (by simp)).clm_apply
      continuous_const)
  have hcac := massive_caccioppoli_cutoff hW hEll hcNonneg hmu hrhoMeas hrhoBdd
    hrhoNonneg u hf hu hchi hchiC hchiS hchi_le hK
  -- the left-hand side dominates the energy on `Q`
  have hcutInt : IntegrableOn (fun x ↦ c x * chi x ^ 2 * vecNormSq (u.grad x)) W :=
    integrableOn_cutoff_energy hWmeas hEll u
      hchi.continuous.aestronglyMeasurable hchi_le
  have hcutNonneg : 0 ≤ᵐ[volume.restrict W]
      fun x ↦ c x * chi x ^ 2 * vecNormSq (u.grad x) := by
    filter_upwards with x
    exact mul_nonneg (mul_nonneg (hcNonneg x) (sq_nonneg _)) (vecNormSq_nonneg _)
  have hinner : ∫ x in Q, c x * vecNormSq (u.grad x) ∂volume ≤
      ∫ x in W, c x * chi x ^ 2 * vecNormSq (u.grad x) ∂volume := by
    have heq : ∫ x in Q, c x * vecNormSq (u.grad x) ∂volume =
        ∫ x in Q, c x * chi x ^ 2 * vecNormSq (u.grad x) ∂volume := by
      refine setIntegral_congr_fun hQmeas fun x hx ↦ ?_
      rw [hchi_one x hx]
      ring
    rw [heq]
    exact setIntegral_mono_set hcutInt hcutNonneg (Filter.Eventually.of_forall hQW)
  -- the cutoff-gradient term
  have hAInt : IntegrableOn
      (fun x ↦ c x * u.toFun x ^ 2 *
        vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i))) W :=
    integrableOn_value_gradSq hWmeas hEll u hgchi_cont hK
  have hA : ∫ x in W, c x * u.toFun x ^ 2 *
        vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume ≤
      K * cMax * M ^ 2 * (volume W).toReal := by
    have hpt : (fun x ↦ c x * u.toFun x ^ 2 *
          vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i))) ≤ᵐ[volume.restrict W]
        fun _ ↦ K * cMax * M ^ 2 := by
      filter_upwards [hM, ae_restrict_mem hWmeas] with x hx hxW
      have hc0 := hcNonneg x
      have hcM := hcLe x hxW
      have hcMax0 : 0 ≤ cMax := le_trans hc0 hcM
      have hu2 : u.toFun x ^ 2 ≤ M ^ 2 := by
        obtain ⟨h1, h2⟩ := abs_le.mp hx
        nlinarith
      have hu20 : (0 : ℝ) ≤ u.toFun x ^ 2 := sq_nonneg _
      have hgK := hK x
      have hcu : c x * u.toFun x ^ 2 ≤ cMax * M ^ 2 := by
        have h1 := mul_le_mul_of_nonneg_right hcM hu20
        have h2 := mul_le_mul_of_nonneg_left hu2 hcMax0
        linarith
      have hcu0 : 0 ≤ c x * u.toFun x ^ 2 := mul_nonneg hc0 hu20
      calc c x * u.toFun x ^ 2 *
              vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i))
          ≤ c x * u.toFun x ^ 2 * K := mul_le_mul_of_nonneg_left hgK hcu0
        _ ≤ cMax * M ^ 2 * K := mul_le_mul_of_nonneg_right hcu hK0
        _ = K * cMax * M ^ 2 := by ring
    have hmono := integral_mono_ae hAInt (integrable_const _) hpt
    rw [setIntegral_const, smul_eq_mul] at hmono
    calc ∫ x in W, c x * u.toFun x ^ 2 *
            vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ∂volume
        ≤ (volume W).toReal * (K * cMax * M ^ 2) := hmono
      _ = K * cMax * M ^ 2 * (volume W).toReal := by ring
  -- the mass term
  have hBInt : IntegrableOn (fun x ↦ rho x * u.toFun x * u.toFun x) W :=
    integrableOn_mass_term hrhoMeas hrhoBdd u.memL2 u.memL2
  have hBb : ∫ x in W, rho x * u.toFun x * u.toFun x ∂volume ≤
      rhoMax * M ^ 2 * (volume W).toReal := by
    have hpt : (fun x ↦ rho x * u.toFun x * u.toFun x) ≤ᵐ[volume.restrict W]
        fun _ ↦ rhoMax * M ^ 2 := by
      filter_upwards [hM, hrhoBdd, ae_restrict_mem hWmeas] with x hx hrho hxW
      have hr0 := hrhoNonneg x hxW
      have hrLe : rho x ≤ rhoMax := le_trans (le_abs_self _) hrho
      have hu2 : u.toFun x * u.toFun x ≤ M ^ 2 := by
        obtain ⟨h1, h2⟩ := abs_le.mp hx
        nlinarith
      have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
      calc rho x * u.toFun x * u.toFun x = rho x * (u.toFun x * u.toFun x) := by ring
        _ ≤ rho x * M ^ 2 := mul_le_mul_of_nonneg_left hu2 hr0
        _ ≤ rhoMax * M ^ 2 := mul_le_mul_of_nonneg_right hrLe hM2
    have hmono := integral_mono_ae hBInt (integrable_const _) hpt
    rw [setIntegral_const, smul_eq_mul] at hmono
    calc ∫ x in W, rho x * u.toFun x * u.toFun x ∂volume
        ≤ (volume W).toReal * (rhoMax * M ^ 2) := hmono
      _ = rhoMax * M ^ 2 * (volume W).toReal := by ring
  nlinarith [hcac, hinner, hA, hBb]

/-- **The Caccioppoli estimate on the centred cube exhaustion.**  Any solution
of the massive equation on `cube d (k+1)` with an almost-everywhere sup bound
`M` has energy on the inner cube `cube d k` bounded by `M`, the forcing on the
outer cube, and the local constants of `MassiveCubeBounds`.

This is the estimate the compact-support exhaustion lacked: the proved
`exists_uniform_local_gradient_norm_bound` controls the energy by `∫ ρ f²` over
the *whole* large cube, which is uniformly finite only for compactly supported
`f`. -/
theorem massive_cube_energy_le [NeZero d] {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) {mu : ℝ} (hmu : 0 ≤ mu) (k : ℕ)
    {f : Vec d → ℝ} (hf : MemL2On (cube d ((k + 1 : ℕ) : ℤ)) f)
    (u : H1Function (cube d ((k + 1 : ℕ) : ℤ)))
    (hu : IsMassiveWeakSolutionOn c rho mu (cube d ((k + 1 : ℕ) : ℤ)) u f)
    {M : ℝ}
    (hM : ∀ᵐ x ∂(volume.restrict (cube d ((k + 1 : ℕ) : ℤ))), |u.toFun x| ≤ M) :
    ∫ x in cube d (k : ℤ), c x * vecNormSq (u.grad x) ∂volume ≤
      (4 * cubeCutoffGradBound d k * B.Lam (k + 1) + B.rhoMax (k + 1)) * M ^ 2 *
          (volume (cube d ((k + 1 : ℕ) : ℤ))).toReal +
        ∫ x in cube d ((k + 1 : ℕ) : ℤ), rho x * f x * f x ∂volume := by
  obtain ⟨chi, hchi, hchi_le, hchi_one, hchiC, hchiS, hchiK⟩ :=
    exists_smooth_cube_cutoff d k
  exact massive_energy_le_of_cutoff
    (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d ((k + 1 : ℕ) : ℤ))
    (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)).isOpen.measurableSet
    (Section6ExcessDecay.cube_subset_cube_of_le (by omega))
    (B.ell (k + 1)) B.coeff_nonneg (fun x hx ↦ B.coeff_le (k + 1) hx) hmu
    (B.rho_measurable (k + 1)) (B.rho_bounded (k + 1))
    (fun x _ ↦ B.weight_nonneg x) u hf hu hM hchi hchiC hchiS hchi_le hchi_one hchiK

/-- **The uniform local gradient bound supplied by the Caccioppoli estimate.**
For a fixed forcing and a fixed sup bound `M`, the Hilbert `L²` gradient norm on
`cube d k` of *every* massive solution on `cube d (k+1)` is bounded by one
constant.  Unlike the proved `exists_uniform_local_gradient_norm_bound` this
uses no compactness of the support of the forcing and no boundary condition. -/
theorem exists_uniform_cube_gradient_bound [NeZero d] {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) {mu : ℝ} (hmu : 0 ≤ mu) (k : ℕ)
    (f : Vec d → ℝ) (M : ℝ) :
    ∃ Cgrad : ℝ, 0 ≤ Cgrad ∧
      ∀ (u : H1Function (cube d ((k + 1 : ℕ) : ℤ)))
        (hQopen : IsOpen (cube d (k : ℤ)))
        (hQW : cube d (k : ℤ) ⊆ cube d ((k + 1 : ℕ) : ℤ)),
        MemL2On (cube d ((k + 1 : ℕ) : ℤ)) f →
        IsMassiveWeakSolutionOn c rho mu (cube d ((k + 1 : ℕ) : ℤ)) u f →
        (∀ᵐ x ∂(volume.restrict (cube d ((k + 1 : ℕ) : ℤ))), |u.toFun x| ≤ M) →
        ‖(u.restrict hQopen hQW).gradToHilbertVectorL2‖ ≤ Cgrad := by
  classical
  refine ⟨Real.sqrt
    (((4 * cubeCutoffGradBound d k * B.Lam (k + 1) + B.rhoMax (k + 1)) * M ^ 2 *
        (volume (cube d ((k + 1 : ℕ) : ℤ))).toReal +
      ∫ x in cube d ((k + 1 : ℕ) : ℤ), rho x * f x * f x ∂volume) / B.lam k),
    Real.sqrt_nonneg _, ?_⟩
  intro u hQopen hQW hf hu hM
  set w : H1Function (cube d (k : ℤ)) := u.restrict hQopen hQW with hw_def
  have hcoercive : B.lam k * ‖w.gradToHilbertVectorL2‖ ^ 2 ≤
      ∫ x in cube d (k : ℤ), c x * vecNormSq (w.grad x) ∂volume := by
    have hcoercive' := MassiveH1Hilbert.coeffGradientBilin_self_ge
      (B.ell k) (MassiveH1Hilbert.ofH1Function w)
    simpa only [MassiveH1Hilbert.gradient_ofH1Function,
      MassiveH1Hilbert.coeffGradientBilin_apply_ofH1Function,
      vecDot_smul_left, vecNormSq] using hcoercive'
  have hgradEq : ∫ x in cube d (k : ℤ), c x * vecNormSq (w.grad x) ∂volume =
      ∫ x in cube d (k : ℤ), c x * vecNormSq (u.grad x) ∂volume := by
    simp only [hw_def, H1Function.restrict]
  have henergy := massive_cube_energy_le B hmu k hf u hu hM
  rw [hgradEq] at hcoercive
  have hsquare : ‖w.gradToHilbertVectorL2‖ ^ 2 ≤
      ((4 * cubeCutoffGradBound d k * B.Lam (k + 1) + B.rhoMax (k + 1)) * M ^ 2 *
          (volume (cube d ((k + 1 : ℕ) : ℤ))).toReal +
        ∫ x in cube d ((k + 1 : ℕ) : ℤ), rho x * f x * f x ∂volume) / B.lam k := by
    refine (le_div_iff₀ (B.lam_pos k)).2 ?_
    calc ‖w.gradToHilbertVectorL2‖ ^ 2 * B.lam k
        = B.lam k * ‖w.gradToHilbertVectorL2‖ ^ 2 := by ring
      _ ≤ ∫ x in cube d (k : ℤ), c x * vecNormSq (u.grad x) ∂volume := hcoercive
      _ ≤ _ := henergy
  exact Real.le_sqrt_of_sq_le hsquare

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
