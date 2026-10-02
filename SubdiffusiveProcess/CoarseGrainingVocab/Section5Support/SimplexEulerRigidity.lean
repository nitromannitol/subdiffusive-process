import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.PointwiseRangeDependence
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn.Interpolation
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open MeasureTheory ProbabilityTheory Homogenization Bornology
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ContDiff

noncomputable section

variable {d : ℕ}

/-! ## Coordinate gradients -/

/-- The coordinate gradient `nabla u` of a scalar function, read off the
Fréchet derivative through the standard basis. -/
def gradVec (u : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => fderiv ℝ u x (Pi.single i 1)

/-- Every vector is the combination of the standard basis with its own
coordinates. -/
private theorem sum_smul_single (p : Vec d) :
    (∑ i, p i • (Pi.single i (1 : ℝ))) = p := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- A continuous linear functional applied to `p` is the dot product of `p`
with the functional's coordinate gradient. -/
theorem vecDot_gradVec_eq_fderiv (u : Vec d → ℝ) (x p : Vec d) :
    vecDot p (gradVec u x) = fderiv ℝ u x p := by
  conv_rhs => rw [← sum_smul_single p]
  rw [map_sum]
  simp [vecDot, gradVec]

/-- The continuous linear functional `x ↦ p ⬝ x`. -/
def linearFnCLM (p : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ i, p i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i

@[simp] theorem linearFnCLM_apply (p x : Vec d) : linearFnCLM p x = vecDot p x := by
  simp [linearFnCLM, vecDot]

theorem hasFDerivAt_linearFn (p x : Vec d) :
    HasFDerivAt (Kuhn.linearFn p) (linearFnCLM p) x := by
  have h : HasFDerivAt (fun y : Vec d => linearFnCLM p y) (linearFnCLM p) x :=
    (linearFnCLM p).hasFDerivAt
  simpa [Kuhn.linearFn] using h

@[simp] theorem gradVec_linearFn (p x : Vec d) : gradVec (Kuhn.linearFn p) x = p := by
  funext i
  simp [gradVec, (hasFDerivAt_linearFn p x).fderiv, vecDot, Pi.single_apply]

theorem gradVec_linearFn_add {p : Vec d} {φ : Vec d → ℝ} {x : Vec d}
    (hφ : DifferentiableAt ℝ φ x) :
    gradVec (fun y => Kuhn.linearFn p y + φ y) x = p + gradVec φ x := by
  have h : HasFDerivAt (fun y => Kuhn.linearFn p y + φ y)
      (linearFnCLM p + fderiv ℝ φ x) x :=
    (hasFDerivAt_linearFn p x).add hφ.hasFDerivAt
  funext i
  simp only [gradVec, Pi.add_apply, h.fderiv, ContinuousLinearMap.add_apply,
    linearFnCLM_apply]
  simp [vecDot, Pi.single_apply]

theorem gradVec_const_mul {t : ℝ} {φ : Vec d → ℝ} {x : Vec d}
    (hφ : DifferentiableAt ℝ φ x) :
    gradVec (fun y => t * φ y) x = t • gradVec φ x := by
  have h : HasFDerivAt (fun y => t * φ y) (t • fderiv ℝ φ x) x := by
    simpa using hφ.hasFDerivAt.const_mul t
  funext i
  simp [gradVec, h.fderiv]

/-! ## Vector algebra for the quadratic expansion -/

theorem vecDot_smul_right (t : ℝ) (a b : Vec d) :
    vecDot a (t • b) = t * vecDot a b := by
  simp [vecDot, Finset.mul_sum, mul_left_comm]

theorem vecNormSq_add (a b : Vec d) :
    vecNormSq (a + b) = vecNormSq a + 2 * vecDot a b + vecNormSq b := by
  simp only [vecNormSq, vecDot, Pi.add_apply]
  rw [Finset.sum_congr rfl (fun i _ =>
    show (a i + b i) * (a i + b i) = a i * a i + 2 * (a i * b i) + b i * b i by ring)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem continuous_vecDot_comp {f : Vec d → Vec d} (hf : Continuous f) (p : Vec d) :
    Continuous fun x => vecDot p (f x) :=
  continuous_finset_sum _ fun i _ =>
    continuous_const.mul ((continuous_apply i).comp hf)

private theorem continuous_vecNormSq_comp {f : Vec d → Vec d} (hf : Continuous f) :
    Continuous fun x => vecNormSq (f x) := by
  simp only [vecNormSq, vecDot]
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp hf).mul ((continuous_apply i).comp hf)

/-! ## The one-cell Dirichlet functional and its affine competitor -/



def dirichletEnergyOn (B : Vec d → ℝ) (U : Set (Vec d)) (u : Vec d → ℝ) : ℝ :=
  ∫ x in U, B x * vecNormSq (gradVec u x)



def IsAffineMinimalOn (B : Vec d → ℝ) (U : Set (Vec d)) (p : Vec d) : Prop :=
  ∀ φ : Vec d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    dirichletEnergyOn B U (Kuhn.linearFn p) ≤
      dirichletEnergyOn B U (fun x => Kuhn.linearFn p x + φ x)

/-- A quadratic in `t` with a minimum at `t = 0` has no linear term. -/
private theorem eq_zero_of_quadratic_nonneg {L Q : ℝ}
    (h : ∀ t : ℝ, 0 ≤ 2 * t * L + t ^ 2 * Q) : L = 0 := by
  by_contra hL
  have hL2 : 0 < L ^ 2 := by positivity
  have hQpos : (0 : ℝ) < |Q| + 1 := by positivity
  set s : ℝ := 1 / (|Q| + 1) with hs
  have hspos : 0 < s := by positivity
  have hsQ : s * Q ≤ 1 := by
    have h1 : Q ≤ |Q| := le_abs_self Q
    have h2 : s * Q ≤ s * |Q| := by nlinarith
    have h3 : s * |Q| ≤ 1 := by
      rw [hs, div_mul_eq_mul_div, one_mul, div_le_one hQpos]
      linarith
    linarith
  have hkey := h (-(s * L))
  have hexp : 2 * (-(s * L)) * L + (-(s * L)) ^ 2 * Q
      = -2 * (s * L ^ 2) + (s * L ^ 2) * (s * Q) := by ring
  rw [hexp] at hkey
  have hpos : 0 < s * L ^ 2 := mul_pos hspos hL2
  have hmul : (s * L ^ 2) * (s * Q) ≤ (s * L ^ 2) * 1 :=
    mul_le_mul_of_nonneg_left hsQ hpos.le
  linarith

/-! ## The first variation -/



theorem fderiv_apply_eq_zero_of_isAffineMinimalOn {B : Vec d → ℝ} {U : Set (Vec d)}
    (hU : IsOpen U) (hB : ContDiff ℝ 1 B) (hBU : IntegrableOn B U volume)
    {p : Vec d} (hmin : IsAffineMinimalOn B U p) :
    ∀ x ∈ U, fderiv ℝ B x p = 0 := by
  have hBcont : Continuous B := hB.continuous
  have hBdiff : Differentiable ℝ B := hB.differentiable le_rfl
  have hBfd : Continuous (fderiv ℝ B) := hB.continuous_fderiv le_rfl
  have hBfp : Continuous fun x => fderiv ℝ B x p :=
    (ContinuousLinearMap.apply ℝ ℝ p).continuous.comp hBfd
  have key : ∀ φ : Vec d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x, φ x • fderiv ℝ B x p = 0 := by
    intro φ hφ hφc hφU
    have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
    have hφfd : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
    have hKcpt : IsCompact (tsupport φ) := hφc
    have hGcont : Continuous (gradVec φ) := by
      refine continuous_pi fun i => ?_
      exact ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ))).continuous).comp' hφfd
    have hgz : ∀ x, x ∉ tsupport φ → gradVec φ x = 0 := by
      intro x hx
      have h0 : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ hx
      funext i
      simp [gradVec, h0]
    set f1 : Vec d → ℝ := fun x => B x * vecDot p (gradVec φ x) with hf1
    set f2 : Vec d → ℝ := fun x => B x * vecNormSq (gradVec φ x) with hf2
    have hf1int : Integrable f1 volume :=
      (hBcont.mul (continuous_vecDot_comp hGcont p)).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hKcpt fun x hx => by simp [hgz x hx, vecDot])
    have hf2int : Integrable f2 volume :=
      (hBcont.mul (continuous_vecNormSq_comp hGcont)).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hKcpt fun x hx => by
          simp [hgz x hx, vecNormSq, vecDot])
    have hE0 : dirichletEnergyOn B U (Kuhn.linearFn p) = ∫ x in U, B x * vecNormSq p := by
      simp [dirichletEnergyOn]
    have hEt : ∀ t : ℝ, dirichletEnergyOn B U (fun x => Kuhn.linearFn p x + t * φ x)
        = (∫ x in U, B x * vecNormSq p) + 2 * t * (∫ x in U, f1 x)
          + t ^ 2 * (∫ x in U, f2 x) := by
      intro t
      have hpt : ∀ x, B x * vecNormSq (gradVec (fun y => Kuhn.linearFn p y + t * φ y) x)
          = B x * vecNormSq p + (2 * t * f1 x + t ^ 2 * f2 x) := by
        intro x
        rw [gradVec_linearFn_add ((hφd x).const_mul t), gradVec_const_mul (hφd x),
          vecNormSq_add, vecDot_smul_right, vecNormSq_smul]
        simp only [hf1, hf2]
        ring
      have hi1 : IntegrableOn (fun x => B x * vecNormSq p) U volume := hBU.mul_const _
      have hi2 : IntegrableOn (fun x => 2 * t * f1 x) U volume :=
        hf1int.integrableOn.const_mul _
      have hi3 : IntegrableOn (fun x => t ^ 2 * f2 x) U volume :=
        hf2int.integrableOn.const_mul _
      have hi23 : IntegrableOn (fun x => 2 * t * f1 x + t ^ 2 * f2 x) U volume := hi2.add hi3
      simp only [dirichletEnergyOn]
      simp_rw [hpt]
      rw [integral_add hi1 hi23, integral_add hi2 hi3, integral_const_mul, integral_const_mul]
      ring
    have hquad : ∀ t : ℝ, 0 ≤ 2 * t * (∫ x in U, f1 x) + t ^ 2 * (∫ x in U, f2 x) := by
      intro t
      have hsub : tsupport (fun x => t * φ x) ⊆ U := by
        refine subset_trans (closure_mono ?_) hφU
        intro x hx
        simp only [Function.mem_support] at hx ⊢
        intro h
        exact hx (by rw [h, mul_zero])
      have hcs : HasCompactSupport fun x => t * φ x :=
        HasCompactSupport.intro hKcpt fun x hx => by
          simp [image_eq_zero_of_notMem_tsupport hx]
      have h1 := hmin (fun x => t * φ x) (contDiff_const.mul hφ) hcs hsub
      rw [hEt t, hE0] at h1
      linarith
    have hL : (∫ x in U, f1 x) = 0 := eq_zero_of_quadratic_nonneg hquad
    have hLglobal : ∫ x, f1 x = 0 := by
      have hcompl := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
        (s := U) (f := f1)
        (fun x hx => by simp [hf1, hgz x (fun h => hx (hφU h)), vecDot])
      rw [← hcompl]
      exact hL
    have hf1eq : ∀ x, f1 x = B x * fderiv ℝ φ x p := by
      intro x
      simp only [hf1]
      rw [vecDot_gradVec_eq_fderiv]
    have hI1 : Integrable (fun x => fderiv ℝ B x p * φ x) volume :=
      (hBfp.mul hφ.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hKcpt fun x hx => by
          simp [image_eq_zero_of_notMem_tsupport hx])
    have hI2 : Integrable (fun x => B x * fderiv ℝ φ x p) volume :=
      (hBcont.mul (((ContinuousLinearMap.apply ℝ ℝ p).continuous).comp
        hφfd)).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hKcpt fun x hx => by
          simp [fderiv_of_notMem_tsupport ℝ hx])
    have hI3 : Integrable (fun x => B x * φ x) volume :=
      (hBcont.mul hφ.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hKcpt fun x hx => by
          simp [image_eq_zero_of_notMem_tsupport hx])
    have hIBP : ∫ x, B x * fderiv ℝ φ x p = - ∫ x, fderiv ℝ B x p * φ x :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hI1 hI2 hI3 hBdiff hφd
    have hzero : ∫ x, fderiv ℝ B x p * φ x = 0 := by
      have h := hLglobal
      simp_rw [hf1eq] at h
      rw [hIBP] at h
      linarith
    calc ∫ x, φ x • fderiv ℝ B x p = ∫ x, fderiv ℝ B x p * φ x := by
          simp_rw [smul_eq_mul, mul_comm]
      _ = 0 := hzero
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (f := fun x => fderiv ℝ B x p) (μ := volume)
    (hBfp.locallyIntegrable.locallyIntegrableOn U) key
  intro x hx
  by_contra hne
  rw [ae_iff] at hae
  have hset : {y | ¬ (y ∈ U → fderiv ℝ B y p = 0)}
      = U ∩ (fun y => fderiv ℝ B y p) ⁻¹' ({0} : Set ℝ)ᶜ := by
    ext y
    simp
  rw [hset] at hae
  have hopen : IsOpen (U ∩ (fun y => fderiv ℝ B y p) ⁻¹' ({0} : Set ℝ)ᶜ) :=
    hU.inter (isClosed_singleton.isOpen_compl.preimage hBfp)
  exact absurd hae (hopen.measure_pos volume ⟨x, hx, hne⟩).ne'

/-! ## The stationarity sweep -/

/-- The derivative carried by a translated potential is the derivative of the
potential at the translated point. -/
theorem deriv_translate (z : Vec d) (g : PotentialField d) (x : Vec d) :
    PotentialField.deriv (PotentialField.translate z g) x =
      PotentialField.deriv g (x + z) := rfl

/-- Vanishing of a fixed directional derivative on an open set is a measurable
event: by continuity it is tested on a countable dense subset. -/
theorem measurableSet_forall_deriv_apply_eq_zero {U : Set (Vec d)} (hU : IsOpen U)
    (p : Vec d) :
    MeasurableSet {g : PotentialField d | ∀ x ∈ U, PotentialField.deriv g x p = 0} := by
  classical
  set z : ℕ → Vec d := TopologicalSpace.denseSeq (Vec d) with hz
  have hdense : DenseRange z := TopologicalSpace.denseRange_denseSeq _
  have hcont : ∀ x : Vec d, Continuous fun g : PotentialField d =>
      PotentialField.deriv g x p :=
    fun x => ((ContinuousLinearMap.apply ℝ ℝ p).continuous).comp'
      (PotentialField.continuous_eval_deriv x)
  have hEq : {g : PotentialField d | ∀ x ∈ U, PotentialField.deriv g x p = 0}
      = ⋂ n : ℕ, ⋂ _ : z n ∈ U,
        {g : PotentialField d | PotentialField.deriv g (z n) p = 0} := by
    ext g
    constructor
    · intro hg
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro n hn
      exact hg _ hn
    · intro hg y hy
      simp only [Set.mem_iInter, Set.mem_setOf_eq] at hg
      have hclosed : IsClosed {x : Vec d | PotentialField.deriv g x p = 0} := by
        have : Continuous fun x : Vec d => PotentialField.deriv g x p :=
          ((ContinuousLinearMap.apply ℝ ℝ p).continuous).comp' (PotentialField.deriv g).continuous
        simpa using isClosed_singleton.preimage this
      refine hclosed.closure_subset (?_ : y ∈ closure {x : Vec d |
        PotentialField.deriv g x p = 0})
      rw [mem_closure_iff]
      intro V hV hyV
      obtain ⟨n, hn⟩ := hdense.exists_mem_open (hV.inter hU) ⟨y, hyV, hy⟩
      exact ⟨z n, hn.1, hg n hn.2⟩
  rw [hEq]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => ?_
  exact (hcont (z n)).measurable (measurableSet_singleton 0)



theorem ae_eval_eq_of_ae_deriv_apply_eq_zero (M : GMCModel d) {U : Set (Vec d)}
    (hU : IsOpen U) (hUne : U.Nonempty) {p : Vec d}
    (h : ∀ᵐ g ∂(zeroPotentialLaw M.P).toMeasure, ∀ x ∈ U,
      PotentialField.deriv g x p = 0) :
    ∀ᵐ g ∂(zeroPotentialLaw M.P).toMeasure, ∀ t : ℝ, g 0 = g (t • p) := by
  classical
  set mu := (zeroPotentialLaw M.P).toMeasure with hmu
  set z : ℕ → Vec d := TopologicalSpace.denseSeq (Vec d) with hz
  have hdense : DenseRange z := TopologicalSpace.denseRange_denseSeq _
  have hstep : ∀ n : ℕ, ∀ᵐ g ∂mu, ∀ x ∈ U,
      PotentialField.deriv g (x + z n) p = 0 := by
    intro n
    have hmap : Measure.map (PotentialField.translate (z n)) mu = mu :=
      M.G1.stationary (z n)
    have hpull := ae_of_ae_map
      (f := PotentialField.translate (z n))
      (PotentialField.measurable_translate (z n)).aemeasurable
      (p := fun g : PotentialField d => ∀ x ∈ U, PotentialField.deriv g x p = 0)
      (by rw [hmap]; exact h)
    filter_upwards [hpull] with g hg x hx
    exact hg x hx
  rw [← ae_all_iff] at hstep
  filter_upwards [hstep] with g hg
  have hall : ∀ y : Vec d, PotentialField.deriv g y p = 0 := by
    intro y
    obtain ⟨x₀, hx₀⟩ := hUne
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
    obtain ⟨n, hn⟩ := hdense.exists_mem_open
      (Metric.isOpen_ball (x := y - x₀) (ε := r)) ⟨y - x₀, Metric.mem_ball_self hr⟩
    have hmem : y - z n ∈ U := by
      refine hball ?_
      rw [Metric.mem_ball, dist_eq_norm]
      have hnorm : ‖y - z n - x₀‖ = ‖z n - (y - x₀)‖ := by
        rw [← norm_neg]
        congr 1
        abel
      rw [hnorm, ← dist_eq_norm]
      exact Metric.mem_ball.1 hn
    have := hg n (y - z n) hmem
    simpa using this
  intro t
  have hderiv : ∀ s : ℝ, HasDerivAt (fun r : ℝ => g (r • p))
      (PotentialField.deriv g (s • p) p) s := by
    intro s
    have hline : HasDerivAt (fun r : ℝ => r • p) p s := by
      simpa using (hasDerivAt_id s).smul_const p
    exact (g.hasFDerivAt (s • p)).comp_hasDerivAt s hline
  have hdiff : Differentiable ℝ fun r : ℝ => g (r • p) :=
    fun s => (hderiv s).differentiableAt
  have hzero : ∀ s : ℝ, _root_.deriv (fun r : ℝ => g (r • p)) s = 0 := by
    intro s
    rw [(hderiv s).deriv, hall]
  have := is_const_of_deriv_eq_zero hdiff hzero 0 t
  simpa using this

/-! ## The shell factor as a `C^1` weight -/

theorem shellFactor_pos (M : GMCModel d) (k : ℕ) (omega : PotentialSample d) (x : Vec d) :
    0 < shellFactor M k omega x :=
  Real.exp_pos _

theorem contDiff_one_shellFactor (M : GMCModel d) (omega : PotentialSample d) :
    ContDiff ℝ 1 (shellFactor M 0 omega) :=
  ContDiff.exp (((omega 0).contDiff_one).sub contDiff_const)

/-- `nabla B_0 = B_0 nabla g_0`; in particular `p . nabla B_0` and
`p . nabla g_0` vanish together. -/
theorem hasFDerivAt_shellFactor (M : GMCModel d) (omega : PotentialSample d) (x : Vec d) :
    HasFDerivAt (shellFactor M 0 omega)
      (shellFactor M 0 omega x • PotentialField.deriv (omega 0) x) x :=
  HasFDerivAt.exp (((omega 0).hasFDerivAt x).sub_const (tauSq M.P))

private theorem integrableOn_of_continuous_of_isBounded {f : Vec d → ℝ}
    (hf : Continuous f) {U : Set (Vec d)} (hU : IsBounded U) :
    IntegrableOn f U volume :=
  (hf.continuousOn.integrableOn_compact hU.isCompact_closure).mono_set subset_closure

private theorem zeroPotentialLaw_eq_map (M : GMCModel d) :
    (zeroPotentialLaw M.P).toMeasure =
      Measure.map (fun omega : PotentialSample d => omega 0) M.P.toMeasure := by
  rw [zeroPotentialLaw, potentialMarginalLaw, ProbabilityMeasure.toMeasure_map]

/-! ## The strict one-cell gap -/



theorem not_ae_isAffineMinimalOn (M : GMCModel d) {U : Set (Vec d)}
    (hU : IsOpen U) (hUne : U.Nonempty) (hUbdd : IsBounded U)
    {p : Vec d} (hp : p ≠ 0) :
    ¬ (∀ᵐ omega ∂M.P.toMeasure, IsAffineMinimalOn (shellFactor M 0 omega) U p) := by
  intro hmin
  have heuler : ∀ᵐ omega ∂M.P.toMeasure, ∀ x ∈ U, PotentialField.deriv (omega 0) x p = 0 := by
    filter_upwards [hmin] with omega homega x hx
    have h := fderiv_apply_eq_zero_of_isAffineMinimalOn hU (contDiff_one_shellFactor M omega)
      (integrableOn_of_continuous_of_isBounded
        (contDiff_one_shellFactor M omega).continuous hUbdd) homega x hx
    rw [(hasFDerivAt_shellFactor M omega x).fderiv] at h
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at h
    rcases mul_eq_zero.1 h with h0 | h0
    · exact absurd h0 (shellFactor_pos M 0 omega x).ne'
    · exact h0
  have hlift : ∀ᵐ g ∂(zeroPotentialLaw M.P).toMeasure, ∀ x ∈ U,
      PotentialField.deriv g x p = 0 := by
    rw [zeroPotentialLaw_eq_map]
    exact (ae_map_iff (measurable_potentialCoordinate 0).aemeasurable
      (measurableSet_forall_deriv_apply_eq_zero hU p)).mpr heuler
  have hsweep := ae_eval_eq_of_ae_deriv_apply_eq_zero M hU hUne hlift
  have hdesc : ∀ᵐ omega ∂M.P.toMeasure, ∀ t : ℝ, omega 0 0 = omega 0 (t • p) := by
    exact ae_of_ae_map (f := fun omega : PotentialSample d => omega 0)
      (measurable_potentialCoordinate 0).aemeasurable
      (p := fun g : PotentialField d => ∀ t : ℝ, g 0 = g (t • p))
      (by rw [← zeroPotentialLaw_eq_map]; exact hsweep)
  have hpn : 0 < euclideanNorm p :=
    (euclideanNorm_nonneg p).lt_of_ne fun h => hp (euclideanNorm_eq_zero_iff.1 h.symm)
  set t : ℝ := (Real.sqrt (d : ℝ) + 1) / euclideanNorm p with ht
  have htnn : 0 ≤ t := div_nonneg (by positivity) hpn.le
  have hsep : Real.sqrt (d : ℝ) < euclideanNorm ((0 : Vec d) - t • p) := by
    rw [zero_sub, euclideanNorm_neg, euclideanNorm_smul, abs_of_nonneg htnn, ht,
      div_mul_cancel₀ _ hpn.ne']
    linarith
  refine not_ae_eq_shellFactor_of_sqrt_dim_lt M hsep ?_
  filter_upwards [hdesc] with omega homega
  simp only [shellFactor, homega t]

/-! ## The paper's cell: one triadic simplex -/

/-- The model ordered simplex is nonempty: order the coordinates by the
position of their index under the permutation. -/
theorem orderedUnitSimplex_nonempty (pi : Equiv.Perm (Fin d)) :
    (Kuhn.orderedUnitSimplex pi).Nonempty := by
  have hd : (0 : ℝ) < 2 * ((d : ℝ) + 1) := by positivity
  refine ⟨fun k => (((pi.symm k).val : ℝ) + 1) / (2 * ((d : ℝ) + 1)) - 1 / 4, ?_, ?_⟩
  · intro i
    have hlt : ((pi.symm i).val : ℝ) < (d : ℝ) := by exact_mod_cast (pi.symm i).isLt
    have hnn : (0 : ℝ) ≤ ((pi.symm i).val : ℝ) := Nat.cast_nonneg _
    have h1 : (0 : ℝ) < (((pi.symm i).val : ℝ) + 1) / (2 * ((d : ℝ) + 1)) := by positivity
    have h2 : (((pi.symm i).val : ℝ) + 1) / (2 * ((d : ℝ) + 1)) < 1 / 2 := by
      rw [div_lt_div_iff₀ hd (by norm_num)]
      linarith
    constructor <;> linarith
  · intro i j hij
    simp only [Equiv.symm_apply_apply]
    have h : ((i.val : ℝ)) < ((j.val : ℝ)) := by exact_mod_cast hij
    have hkey : (((i.val : ℝ)) + 1) / (2 * ((d : ℝ) + 1))
        < (((j.val : ℝ)) + 1) / (2 * ((d : ℝ) + 1)) := by
      rw [div_lt_div_iff₀ hd hd]
      nlinarith [hd, h]
    linarith

theorem triadicSimplex_nonempty (n : ℤ) (z : Vec d) (pi : Equiv.Perm (Fin d)) :
    (Kuhn.triadicSimplex n z pi).Nonempty :=
  (orderedUnitSimplex_nonempty pi).image _

/-- **The strict gap on one triadic simplex.**  Specialization of
`not_ae_isAffineMinimalOn` to the source's cell `spx_n^pi(z)`. -/
theorem not_ae_isAffineMinimalOn_kuhnCell (M : GMCModel d) (T : Kuhn.KuhnCell d)
    {p : Vec d} (hp : p ≠ 0) :
    ¬ (∀ᵐ omega ∂M.P.toMeasure,
        IsAffineMinimalOn (shellFactor M 0 omega) T.openCarrier p) :=
  not_ae_isAffineMinimalOn M (Kuhn.isOpen_openCarrier T)
    (by rw [Kuhn.KuhnCell.openCarrier]; exact triadicSimplex_nonempty _ _ _)
    ((isBounded_openCubeSet T.supportCube).subset T.openCarrier_subset_openCubeSet) hp



theorem not_ae_isAffineMinimalOn_originSimplex (M : GMCModel d)
    (pi : Equiv.Perm (Fin d)) {p : Vec d} (hp : p ≠ 0) :
    ¬ (∀ᵐ omega ∂M.P.toMeasure, IsAffineMinimalOn (shellFactor M 0 omega)
        (Kuhn.KuhnCell.mk (originCube d 0) pi).openCarrier p) :=
  not_ae_isAffineMinimalOn_kuhnCell M _ hp

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
