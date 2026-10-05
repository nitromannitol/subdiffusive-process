module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeBoundedAnchor

@[expose] public section

/-!
# The frozen anchor from a *dense* set of `C₀` residuals

`TimeChangeBoundedAnchor.isIntrinsicTimeChange_of_clockDivergence_of_c0Residual` derives the frozen anchor from two
inputs beyond the frozen hypotheses: almost-sure divergence of the reciprocal
clock `(R1)`, and the `C₀` residual condition

  `(C0)  ∀ theta mu f,  a⁻¹ (mu R^{(a,1)}_mu f − f) ∈ C₀(ℝᵈ)`,

which is the assertion `R^{(a,1)}_mu f ∈ D(L_X)` for **every** datum `f`, i.e.
`D(L_Y) ⊆ D(L_X)`.

This file weakens `(C0)` to a density statement.  Both sides of the manuscript's
resolvent identity,

  `f ↦ ∫₀^∞ e^{-mu t} E_y f(Y_t) dt`   and   `f ↦ R^{(a,1)}_mu f (y)`,

are linear in `f` and bounded by `mu⁻¹ ‖f‖`: the left one because the
time-changed process is a probability law at every time
(`abs_timeChangedMarginal_le`), the right one by the contraction half of the
maximum principle (`C0ResolventDatum.norm_solution_le`).  An identity between two
`mu⁻¹`-Lipschitz functions that holds on a dense set of data holds everywhere,
so it is enough to exhibit the `C₀` witness for `f` in a **dense** subset of
`C₀(ℝᵈ)`:

  `(C0′)  ∀ theta mu,  {f | a⁻¹ (mu R^{(a,1)}_mu f − f) ∈ C₀} is dense in C₀`.

Equivalently: `D(L_X) ∩ D(L_Y)` is a core for `L_Y`.  This is strictly weaker
than `(C0)`, which asks the same set to be everything.

## Main declarations

* `timeChangedLaplace` — the `mu`-Laplace transform of the one-dimensional
  marginals of the time-changed process, as a function of the test datum.
* `abs_timeChangedLaplace_sub_le`, `abs_solution_sub_le` — the two Lipschitz
  bounds.
* `timeChangedLaplace_eq_solution_of_dense` — the density transfer.
* `isIntrinsicTimeChange_of_clockDivergence_of_denseC0Residual` — the frozen
  conclusion from `(R1)` and `(C0′)`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.Frozen.Section7
open scoped ENNReal NNReal ZeroAtInfty Topology

noncomputable section

section Marginal

variable {Theta : Type*} {d : ℕ} {a : Theta → State d → ℝ} {theta : Theta}
variable {P : SubMarkovKernelSemigroup (State d)}

/-! ### The Laplace transform of the time-changed marginals -/

/-- The `mu`-Laplace transform of the one-dimensional marginals of the
time-changed process, read as a function of the `C₀` test datum. -/
def timeChangedLaplace (P : SubMarkovKernelSemigroup (State d)) (hP : P.IsConservative)
    (a : Theta → State d → ℝ) (theta : Theta)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) (mu : ℝ) (f : C₀(State d, ℝ)) (y : State d) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-(mu * t)) *
    timeChangedMarginal P hP a theta ha hapos default f y t

theorem timeChangedLaplace_eq (hP : P.IsConservative)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) (mu : ℝ) (f : C₀(State d, ℝ)) (y : State d) :
    timeChangedLaplace P hP a theta ha hapos default mu f y =
      ∫ t in Ioi (0 : ℝ), Real.exp (-(mu * t)) *
        (∫ omega, f (measurableTimeChangedContinuousPath a theta ha hapos default omega
            (Real.toNNReal t))
          ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP y)) := by
  simp only [timeChangedLaplace]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  rw [timeChangedMarginal_eq_integral hP ha hapos default f y t]

/-- The integrand of the Laplace transform is integrable on the half line. -/
theorem integrableOn_timeChangedLaplace_integrand (hP : P.IsConservative)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) {mu : ℝ} (hmu : 0 < mu) (f : C₀(State d, ℝ))
    (y : State d) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-(mu * t)) *
      timeChangedMarginal P hP a theta ha hapos default f y t) (Ioi (0 : ℝ)) := by
  have hcont : Continuous (timeChangedMarginal P hP a theta ha hapos default f y) :=
    continuous_timeChangedMarginal hP ha hapos default f y
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi (0 : ℝ) hmu).const_mul ‖f.toBCF‖)
    (((Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).mul
      hcont).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun t ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul]
  have hb := abs_timeChangedMarginal_le hP ha hapos default f y t
  have hpos : (0 : ℝ) < Real.exp (-(mu * t)) := Real.exp_pos _
  nlinarith [hb, hpos]

/-- The Laplace transform is additive in the datum. -/
theorem timeChangedLaplace_sub (hP : P.IsConservative)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) {mu : ℝ} (hmu : 0 < mu) (f g : C₀(State d, ℝ))
    (y : State d) :
    timeChangedLaplace P hP a theta ha hapos default mu f y -
        timeChangedLaplace P hP a theta ha hapos default mu g y =
      timeChangedLaplace P hP a theta ha hapos default mu (f - g) y := by
  simp only [timeChangedLaplace]
  rw [← integral_sub (integrableOn_timeChangedLaplace_integrand hP ha hapos default hmu f y)
      (integrableOn_timeChangedLaplace_integrand hP ha hapos default hmu g y)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  have hsub := timeChangedMarginal_smul_sub (P := P) hP ha hapos default (1 : ℝ) f g y t
  simp only [one_smul, one_mul] at hsub
  rw [hsub]
  ring

/-- The Laplace transform is bounded by `‖f‖` times the mass of the exponential
weight. -/
theorem abs_timeChangedLaplace_le (hP : P.IsConservative)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) {mu : ℝ} (hmu : 0 < mu) (f : C₀(State d, ℝ))
    (y : State d) :
    |timeChangedLaplace P hP a theta ha hapos default mu f y| ≤
      (∫ t in Ioi (0 : ℝ), Real.exp (-(mu * t))) * ‖f‖ := by
  have hexp : IntegrableOn (fun t : ℝ ↦ Real.exp (-(mu * t))) (Ioi (0 : ℝ)) := by
    have h := exp_neg_integrableOn_Ioi (0 : ℝ) hmu
    simpa only [neg_mul] using h
  have hint := integrableOn_timeChangedLaplace_integrand hP ha hapos default hmu f y
  simp only [timeChangedLaplace]
  refine (abs_integral_le_integral_abs).trans ?_
  have hmono : ∫ t in Ioi (0 : ℝ), |Real.exp (-(mu * t)) *
      timeChangedMarginal P hP a theta ha hapos default f y t| ≤
      ∫ t in Ioi (0 : ℝ), Real.exp (-(mu * t)) * ‖f‖ := by
    refine integral_mono hint.abs (hexp.mul_const ‖f‖) fun t ↦ ?_
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hb := abs_timeChangedMarginal_le hP ha hapos default f y t
    rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at hb
    have hpos : (0 : ℝ) < Real.exp (-(mu * t)) := Real.exp_pos _
    nlinarith [hb, hpos]
  refine hmono.trans_eq ?_
  rw [integral_mul_const]

/-- The Lipschitz bound for the Laplace transform. -/
theorem abs_timeChangedLaplace_sub_le (hP : P.IsConservative)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) {mu : ℝ} (hmu : 0 < mu) (f g : C₀(State d, ℝ))
    (y : State d) :
    |timeChangedLaplace P hP a theta ha hapos default mu f y -
        timeChangedLaplace P hP a theta ha hapos default mu g y| ≤
      (∫ t in Ioi (0 : ℝ), Real.exp (-(mu * t))) * ‖f - g‖ := by
  rw [timeChangedLaplace_sub hP ha hapos default hmu f g y]
  exact abs_timeChangedLaplace_le hP ha hapos default hmu (f - g) y

/-! ### The Lipschitz bound for the resolvent datum -/

/-- Evaluation of a `C₀` function is bounded by its norm. -/
theorem abs_apply_le_norm (f : C₀(State d, ℝ)) (x : State d) : |f x| ≤ ‖f‖ := by
  have h := f.toBCF.norm_coe_le_norm x
  rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at h
  simpa only [Real.norm_eq_abs, ZeroAtInftyContinuousMap.toBCF] using! h

/-- The resolvent of a `C₀` datum is `mu⁻¹`-Lipschitz at every point. -/
theorem abs_solution_sub_le (D : C0ResolventDatum (State d))
    (mu : MarkovProcess.Semigroup.PositiveShift) (f g : C₀(State d, ℝ)) (y : State d) :
    |D.solution mu f y - D.solution mu g y| ≤ ((mu : ℝ))⁻¹ * ‖f - g‖ := by
  have hadd : D.solution mu f = D.solution mu g + D.solution mu (f - g) := by
    rw [← D.solution_add mu g (f - g)]
    congr 1
    abel
  have hval : D.solution mu f y - D.solution mu g y = D.solution mu (f - g) y := by
    rw [hadd]
    simp
  rw [hval]
  exact (abs_apply_le_norm _ y).trans (D.norm_solution_le mu (f - g))


/-! ### Sufficient conditions for the `C₀` residual -/

/-- **The residual from a growth weight.**  If `a⁻¹` is dominated by a
continuous weight `v` and the residual `mu g − f` decays faster than `v` grows,
then the reciprocal-weighted residual is a `C₀` function.  This is the shape in
which the whole-space resolvent estimates of Section 8
discharge `(C0)`. -/
theorem exists_c0_residual_of_weight {b : State d → ℝ} (hcont : Continuous b)
    (hpos : ∀ x, 0 < b x) {v : State d → ℝ} (hle : ∀ x, (b x)⁻¹ ≤ v x)
    (mu : ℝ) (f g : C₀(State d, ℝ))
    (hdecay : Filter.Tendsto (fun x ↦ v x * |mu * g x - f x|)
      (Filter.cocompact (State d)) (nhds 0)) :
    ∃ k : C₀(State d, ℝ), ∀ x, k x = (b x)⁻¹ * (mu * g x - f x) := by
  have hbinv : Continuous fun x ↦ (b x)⁻¹ := hcont.inv₀ fun x ↦ ne_of_gt (hpos x)
  have hk : Continuous fun x ↦ (b x)⁻¹ * (mu * g x - f x) :=
    hbinv.mul ((continuous_const.mul g.continuous).sub f.continuous)
  refine ⟨⟨⟨_, hk⟩, ?_⟩, fun x ↦ rfl⟩
  refine squeeze_zero_norm (a := fun x ↦ v x * |mu * g x - f x|) (fun x ↦ ?_) hdecay
  have hbx : (0 : ℝ) < (b x)⁻¹ := inv_pos.2 (hpos x)
  have habs : ‖(b x)⁻¹ * (mu * g x - f x)‖ = (b x)⁻¹ * |mu * g x - f x| := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hbx]
  rw [habs]
  exact mul_le_mul_of_nonneg_right (hle x) (abs_nonneg _)

/-! ### The two obstructions are conditions at infinity only -/

/-- A positive continuous function bounded below off a compact set is bounded
below. -/
theorem exists_pos_lowerBound_of_cocompact {b : State d → ℝ} (hcont : Continuous b)
    (hpos : ∀ x, 0 < b x) {eps : ℝ} (heps : 0 < eps)
    (hev : ∀ᶠ x in Filter.cocompact (State d), eps ≤ b x) :
    ∃ eps' : ℝ, 0 < eps' ∧ ∀ x, eps' ≤ b x := by
  obtain ⟨K, hK, hKle⟩ := Filter.hasBasis_cocompact.eventually_iff.1 hev
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨eps, heps, fun x ↦ hKle (by simp [hKe])⟩
  · obtain ⟨x0, hx0K, hx0⟩ := hK.exists_isMinOn hKne hcont.continuousOn
    refine ⟨min eps (b x0), lt_min heps (hpos x0), fun x ↦ ?_⟩
    by_cases hx : x ∈ K
    · exact le_trans (min_le_right _ _) (hx0 hx)
    · exact le_trans (min_le_left _ _) (hKle hx)

/-- A continuous function bounded above off a compact set is bounded above. -/
theorem exists_pos_upperBound_of_cocompact {b : State d → ℝ} (hcont : Continuous b)
    {C : ℝ} (hC : 0 < C)
    (hev : ∀ᶠ x in Filter.cocompact (State d), b x ≤ C) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ x, b x ≤ C' := by
  obtain ⟨K, hK, hKle⟩ := Filter.hasBasis_cocompact.eventually_iff.1 hev
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨C, hC, fun x ↦ hKle (by simp [hKe])⟩
  · obtain ⟨x0, hx0K, hx0⟩ := hK.exists_isMaxOn hKne hcont.continuousOn
    refine ⟨max C (b x0), lt_max_of_lt_left hC, fun x ↦ ?_⟩
    by_cases hx : x ∈ K
    · exact le_trans (hx0 hx) (le_max_right _ _)
    · exact le_trans (hKle hx) (le_max_left _ _)

/-! ### The density transfer -/

/-- **The resolvent identity from a dense set of data.**  Both sides are
Lipschitz in the datum, so the identity propagates from a dense set. -/
theorem timeChangedLaplace_eq_solution_of_dense (hP : P.IsConservative)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) (D : C0ResolventDatum (State d))
    (mu : MarkovProcess.Semigroup.PositiveShift) {S : Set C₀(State d, ℝ)} (hS : Dense S)
    (hid : ∀ f ∈ S, ∀ y : State d,
      timeChangedLaplace P hP a theta ha hapos default (mu : ℝ) f y = D.solution mu f y)
    (f : C₀(State d, ℝ)) (y : State d) :
    timeChangedLaplace P hP a theta ha hapos default (mu : ℝ) f y = D.solution mu f y := by
  set C : ℝ := ∫ t in Ioi (0 : ℝ), Real.exp (-((mu : ℝ) * t)) with hC
  have hCnonneg : 0 ≤ C := by
    rw [hC]
    exact integral_nonneg fun t ↦ (Real.exp_pos _).le
  have hmuinv : (0 : ℝ) < ((mu : ℝ))⁻¹ := inv_pos.2 mu.property
  set K : ℝ := C + ((mu : ℝ))⁻¹ with hK
  have hKpos : 0 < K := by rw [hK]; linarith
  have hzero : ∀ eps : ℝ, 0 < eps →
      |timeChangedLaplace P hP a theta ha hapos default (mu : ℝ) f y - D.solution mu f y| ≤
        K * eps := by
    intro eps heps
    obtain ⟨g, hgS, hgd⟩ := Metric.mem_closure_iff.1 (hS f) eps heps
    have hnorm : ‖f - g‖ ≤ eps := by
      rw [← dist_eq_norm]
      exact hgd.le
    have hb1 : |timeChangedLaplace P hP a theta ha hapos default (mu : ℝ) f y -
        timeChangedLaplace P hP a theta ha hapos default (mu : ℝ) g y| ≤ C * eps :=
      (abs_timeChangedLaplace_sub_le hP ha hapos default mu.property f g y).trans
        (mul_le_mul_of_nonneg_left hnorm hCnonneg)
    have hb2 : |D.solution mu f y - D.solution mu g y| ≤ ((mu : ℝ))⁻¹ * eps :=
      (abs_solution_sub_le D mu f g y).trans (mul_le_mul_of_nonneg_left hnorm hmuinv.le)
    have h3 := hid g hgS y
    obtain ⟨hb1l, hb1r⟩ := abs_le.1 hb1
    obtain ⟨hb2l, hb2r⟩ := abs_le.1 hb2
    rw [abs_le, hK]
    constructor <;> nlinarith [hb1l, hb1r, hb2l, hb2r, h3]
  have hle : |timeChangedLaplace P hP a theta ha hapos default (mu : ℝ) f y -
      D.solution mu f y| ≤ 0 := by
    refine le_of_forall_pos_le_add fun eps heps ↦ ?_
    have h := hzero (eps / K) (by positivity)
    have hcancel : K * (eps / K) = eps := by
      field_simp
    rw [hcancel] at h
    linarith
  have habs := abs_nonpos_iff.1 hle
  linarith [sub_eq_zero.mp habs]

end Marginal

/-! ### The frozen anchor from a dense residual set -/

/-- **The frozen anchor from clock divergence and a dense set of `C₀`
residuals.**  This weakens hypothesis `(C0)` — the residual
`a⁻¹ (mu R^{(a,1)}_mu f − f)` vanishes at infinity for *every* datum `f`, i.e.
`D(L_Y) ⊆ D(L_X)` — to the assertion that the data with that property are
**dense** in `C₀(ℝᵈ)`, i.e. that `D(L_X) ∩ D(L_Y)` is a core for `L_Y`.

Both sides of the manuscript's resolvent identity
 are `mu⁻¹`-Lipschitz in the datum, so
the identity extends from the dense set to all of `C₀`. -/
theorem isIntrinsicTimeChange_of_clockDivergence_of_denseC0Residual
    {Theta : Type*} [MeasurableSpace Theta] {d : ℕ}
    (a : Theta → State d → ℝ)
    (ha_pos : ∀ theta x, 0 < a theta x) (ha_cont : ∀ theta, Continuous (a theta))
    {DXDatum DYDatum : Theta →
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (State d)}
    (DX : GeneratedDiffusionFamily Theta d a a DXDatum)
    (DY : GeneratedDiffusionFamily Theta d a (fun _ _ ↦ 1) DYDatum)
    (PX : CemeteryDiffusion d DX) (PY : CemeteryDiffusion d DY)
    (default : Theta → ContinuousPath (State d))
    (hresidual : ∀ (theta : Theta) (mu : MarkovProcess.Semigroup.PositiveShift),
      Dense {f : C₀(State d, ℝ) | ∃ k : C₀(State d, ℝ), ∀ x,
        k x = (a theta x)⁻¹ * ((mu : ℝ) * (DYDatum theta).solution mu f x - f x)})
    (hunbounded : ∀ theta y, ∀ᵐ omega ∂
      ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess
        DX.semigroup DX.conservative (theta, y),
      omega ∈ timeChangeUnboundedEvent a theta) :
    IsIntrinsicTimeChange a
      (Kernel.toLifetimePathKernel PX.law)
      (Kernel.toLifetimePathKernel PY.law) := by
  refine isIntrinsicTimeChange_of_clockDivergence_of_resolventIdentity a ha_pos ha_cont
    DX DY PX PY default hunbounded ?_
  intro theta f mu y
  set P := DX.semigroup.toSubMarkovKernelSemigroup theta with hPdef
  have hPeq : P = (DXDatum theta).fellerKernelSemigroup (DX.denseRange theta) :=
    DX.semigroup_eq theta
  have hFeller : P.IsFellerKernelSemigroup := by
    rw [hPeq]
    exact (DXDatum theta).isFellerKernelSemigroup_fellerKernelSemigroup (DX.denseRange theta)
  obtain ⟨p, q, M, hmom⟩ := DX.displacementMoments
  have hK := ParameterizedSubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments
    DX.semigroup DX.conservative hmom theta
  have hdivall : ∀ z : State d, ∀ᵐ omega ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess
      P (DX.conservative theta) z), omega ∈ timeChangeUnboundedEvent a theta := by
    intro z
    have h := hunbounded theta z
    rwa [ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_apply
      DX.semigroup DX.conservative theta z] at h
  have hidS : ∀ g ∈ {f : C₀(State d, ℝ) | ∃ k : C₀(State d, ℝ), ∀ x,
        k x = (a theta x)⁻¹ * ((mu : ℝ) * (DYDatum theta).solution mu f x - f x)},
      ∀ z : State d,
      timeChangedLaplace P (DX.conservative theta) a theta (ha_cont theta) (ha_pos theta)
          (default theta) (mu : ℝ) g z = (DYDatum theta).solution mu g z := by
    rintro g ⟨k, hk⟩ z
    have hmem : (DYDatum theta).solution mu g ∈ hFeller.c0Semigroup.generatorDomain :=
      mem_generatorDomain_solution_divergence_of_c0 (ha_cont theta) (ha_pos theta)
        (DX.denseRange theta) (DX.weakResolvent theta) (DY.weakResolvent theta) hFeller hPeq
        mu g k hk
    have hgen := generator_solution_divergence_of_c0 (ha_cont theta) (ha_pos theta)
      (DX.denseRange theta) (DX.weakResolvent theta) (DY.weakResolvent theta) hFeller hPeq
      mu g k hk hmem
    have hmain := timeChanged_resolvent_identity_of_divergence (a := a) (theta := theta)
      (DX.conservative theta) hFeller hK (ha_cont theta) (ha_pos theta) (default theta)
      mu.property ((DYDatum theta).solution mu g) g hmem hgen z (hdivall z)
    rw [timeChangedLaplace_eq (DX.conservative theta) (ha_cont theta) (ha_pos theta)
      (default theta) (mu : ℝ) g z]
    exact hmain
  have hall := timeChangedLaplace_eq_solution_of_dense (DX.conservative theta) (ha_cont theta)
    (ha_pos theta) (default theta) (DYDatum theta) mu (hresidual theta mu) hidS f y
  rw [timeChangedLaplace_eq (DX.conservative theta) (ha_cont theta) (ha_pos theta)
    (default theta) (mu : ℝ) f y] at hall
  rw [← ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_apply
    DX.semigroup DX.conservative theta y] at hall
  simpa only [neg_mul] using hall

/-- **The frozen anchor for a coefficient two-sidedly bounded at infinity.**  A
continuous positive coefficient is automatically two-sidedly bounded on every
compact set, so both of obstructions — the `C₀` residual `(C0)` and the
clock divergence `(R1)` — are conditions at infinity only. -/
theorem isIntrinsicTimeChange_of_boundedCoefficient_cocompact
    {Theta : Type*} [MeasurableSpace Theta] {d : ℕ}
    (a : Theta → State d → ℝ)
    (ha_pos : ∀ theta x, 0 < a theta x) (ha_cont : ∀ theta, Continuous (a theta))
    {DXDatum DYDatum : Theta →
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (State d)}
    (DX : GeneratedDiffusionFamily Theta d a a DXDatum)
    (DY : GeneratedDiffusionFamily Theta d a (fun _ _ ↦ 1) DYDatum)
    (PX : CemeteryDiffusion d DX) (PY : CemeteryDiffusion d DY)
    (default : Theta → ContinuousPath (State d))
    (hupper : ∀ theta, ∃ C : ℝ, 0 < C ∧
      ∀ᶠ x in Filter.cocompact (State d), a theta x ≤ C)
    (hlower : ∀ theta, ∃ eps : ℝ, 0 < eps ∧
      ∀ᶠ x in Filter.cocompact (State d), eps ≤ a theta x) :
    IsIntrinsicTimeChange a
      (Kernel.toLifetimePathKernel PX.law)
      (Kernel.toLifetimePathKernel PY.law) := by
  refine isIntrinsicTimeChange_of_boundedCoefficient a ha_pos ha_cont DX DY PX PY default
    (fun theta ↦ ?_) (fun theta ↦ ?_)
  · obtain ⟨C, hC, hev⟩ := hupper theta
    exact exists_pos_upperBound_of_cocompact (ha_cont theta) hC hev
  · obtain ⟨eps, heps, hev⟩ := hlower theta
    exact exists_pos_lowerBound_of_cocompact (ha_cont theta) (ha_pos theta) heps hev

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
