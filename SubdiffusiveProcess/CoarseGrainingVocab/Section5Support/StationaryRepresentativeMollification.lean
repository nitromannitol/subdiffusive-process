module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationarySetTransfer
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryMollifierDerivative

@[expose] public section

/-!
# Samplewise mollification of stationary representatives

This is the representative-level companion to `Stationary.mollifyL2`.  It
mirrors the `Mollification` / `MollifiedPrimitive` pair in Superdiffusion's
corrector provider: the sign in the stationary convolution makes its spatial
realization the ordinary Euclidean convolution.  Consequently a compactly
supported smooth kernel produces a smooth spatial primitive with an explicit
gradient representative.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- Mollification of a representative along the literal GMC translation
action. -/
def representativeMollify {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (kappa : Vec d → ℝ) (X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : E :=
  ∫ y : Vec d, kappa y • X ((-y) +ᵥ omega)

/-- The realization of the representative mollification is ordinary
Euclidean convolution. -/
theorem realize_representativeMollify {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (kappa : Vec d → ℝ) (X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    realize (representativeMollify kappa X) omega =
      convolution kappa (realize X omega)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext x
  have hshift : ∀ y : Vec d,
      (-y) +ᵥ (x +ᵥ omega) = (x - y) +ᵥ omega := by
    intro y
    rw [vadd_vadd, neg_add_eq_sub]
  simp only [realize, representativeMollify, convolution_def,
    ContinuousLinearMap.lsmul_apply, hshift]

/-- For almost every GMC sample, the realization of a stationary `L²`
representative is locally integrable. -/
theorem ae_locallyIntegrable_realize {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {E : Type*} [NormedAddCommGroup E]
    {X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 M.P.toMeasure) :
    ∀ᵐ omega ∂M.P.toMeasure,
      LocallyIntegrable (realize X omega) volume := by
  have hball : ∀ n : ℕ,
      volume (Metric.closedBall (0 : Vec d) (n : ℝ)) ≠ ⊤ := fun n =>
    (isCompact_closedBall (0 : Vec d) (n : ℝ)).measure_lt_top.ne
  have hae : ∀ n : ℕ, ∀ᵐ omega ∂M.P.toMeasure,
      MemLp (realize X omega) 2
        (volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))) :=
    fun n => ae_memLp_two_realize M (hball n) hXm hX
  rw [← ae_all_iff] at hae
  filter_upwards [hae] with omega homega
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt (‖x‖ + 1)
  haveI : IsFiniteMeasure
      (volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 (hball n)
  have hint : IntegrableOn (realize X omega)
      (Metric.closedBall (0 : Vec d) (n : ℝ)) volume :=
    (homega n).integrable (by norm_num)
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, hint.mono_set ?_⟩
  intro z hz
  have hz1 : dist z x < 1 := Metric.mem_ball.1 hz
  have hzNorm : ‖z‖ ≤ ‖x‖ + 1 := by
    have hnorm := norm_sub_norm_le z x
    have hdist : ‖z - x‖ < 1 := by rwa [← dist_eq_norm]
    linarith
  exact Metric.mem_closedBall.2 (by
    rw [dist_eq_norm, sub_zero]
    linarith)

private theorem sq_weighted_integral_le
    {alpha : Type*} [MeasurableSpace alpha] {nu : Measure alpha}
    {rho g : alpha → ℝ} (hrho0 : ∀ a, 0 ≤ rho a)
    (hrho : Integrable rho nu)
    (h1 : Integrable (fun a => rho a * g a) nu)
    (h2 : Integrable (fun a => rho a * g a ^ 2) nu) :
    (∫ a, rho a * g a ∂nu) ^ 2 ≤
      (∫ a, rho a ∂nu) * ∫ a, rho a * g a ^ 2 ∂nu := by
  have hexpand : ∀ c : ℝ,
      ∫ a, rho a * (g a - c) ^ 2 ∂nu =
        ((∫ a, rho a * g a ^ 2 ∂nu) -
          2 * c * ∫ a, rho a * g a ∂nu) +
        c ^ 2 * ∫ a, rho a ∂nu := by
    intro c
    have hpoint : ∀ a,
        rho a * (g a - c) ^ 2 =
          rho a * g a ^ 2 - 2 * c * (rho a * g a) + c ^ 2 * rho a := by
      intro a
      ring
    have hmul1 : Integrable (fun a => 2 * c * (rho a * g a)) nu :=
      h1.const_mul (2 * c)
    have hmul2 : Integrable (fun a => c ^ 2 * rho a) nu :=
      hrho.const_mul (c ^ 2)
    have hleft : Integrable
        (fun a => rho a * g a ^ 2 - 2 * c * (rho a * g a)) nu :=
      h2.sub hmul1
    calc
      ∫ a, rho a * (g a - c) ^ 2 ∂nu =
          ∫ a, ((rho a * g a ^ 2 - 2 * c * (rho a * g a)) +
            c ^ 2 * rho a) ∂nu := by simp only [hpoint]
      _ = (∫ a, (rho a * g a ^ 2 - 2 * c * (rho a * g a)) ∂nu) +
          ∫ a, c ^ 2 * rho a ∂nu := integral_add hleft hmul2
      _ = _ := by
        rw [integral_sub h2 hmul1, integral_const_mul, integral_const_mul]
  have hquad : ∀ c : ℝ,
      0 ≤ (∫ a, rho a ∂nu) * (c * c) +
        (-2 * ∫ a, rho a * g a ∂nu) * c +
        ∫ a, rho a * g a ^ 2 ∂nu := by
    intro c
    have hnonneg : 0 ≤ ∫ a, rho a * (g a - c) ^ 2 ∂nu :=
      integral_nonneg fun a => mul_nonneg (hrho0 a) (sq_nonneg _)
    rw [hexpand c] at hnonneg
    nlinarith
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith

/-- Joint integrability of an integrable stationary scalar observable against
an integrable spatial weight. -/
theorem integrable_prod_weighted_representativeTranslate {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {rho : Vec d → ℝ} (hrhom : Continuous rho)
    (hrho : Integrable rho volume)
    {g : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ} (hgm : StronglyMeasurable g)
    (hg : Integrable g M.P.toMeasure) :
    Integrable
      (fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
        rho q.2 * g ((-q.2) +ᵥ q.1))
      (M.P.toMeasure.prod volume) := by
  have hshift : Measurable fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
      (-q.2) +ᵥ q.1 :=
    measurable_vadd.comp (measurable_snd.neg.prodMk measurable_fst)
  have hjoint : StronglyMeasurable fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
      rho q.2 * g ((-q.2) +ᵥ q.1) :=
    ((hrhom.measurable.comp measurable_snd).stronglyMeasurable).mul
      (hgm.comp_measurable hshift)
  refine (integrable_prod_iff' hjoint.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall fun y =>
      (integrable_realize M hg (-y)).const_mul (rho y)
  · refine (integrable_congr ?_).2
      (hrho.abs.mul_const (∫ omega, ‖g omega‖ ∂M.P.toMeasure))
    filter_upwards with y
    simp only [norm_mul, Real.norm_eq_abs]
    rw [integral_const_mul]
    exact congrArg (fun t => |rho y| * t)
      (integral_realize M (fun omega => ‖g omega‖) (-y))

/-- A representative mollification is strongly measurable. -/
theorem stronglyMeasurable_representativeMollify {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    {X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E} (hXm : StronglyMeasurable X) :
    StronglyMeasurable (representativeMollify kappa X) := by
  have hshift : Measurable fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
      (-q.2) +ᵥ q.1 :=
    measurable_vadd.comp (measurable_snd.neg.prodMk measurable_fst)
  have hjoint : StronglyMeasurable fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
      kappa q.2 • X ((-q.2) +ᵥ q.1) :=
    ((hkappa.measurable.comp measurable_snd).stronglyMeasurable).smul
      (hXm.comp_measurable hshift)
  exact hjoint.integral_prod_right'

/-- Representative mollification preserves the stationary `L²` class. -/
theorem memLp_two_representativeMollify {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hkappaInt : Integrable kappa volume)
    {X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 M.P.toMeasure) :
    MemLp (representativeMollify kappa X) 2 M.P.toMeasure := by
  have hsq : Integrable (fun omega => ‖X omega‖ ^ 2) M.P.toMeasure :=
    (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX
  have hprod := integrable_prod_weighted_representativeTranslate M
    hkappa.abs hkappaInt.abs (hXm.norm.pow 2) hsq
  have hdom : Integrable (fun omega =>
      (∫ y, |kappa y|) *
        ∫ y, |kappa y| * ‖X ((-y) +ᵥ omega)‖ ^ 2) M.P.toMeasure :=
    hprod.integral_prod_left.const_mul _
  have hpoint : ∀ᵐ omega ∂M.P.toMeasure,
      ‖representativeMollify kappa X omega‖ ^ 2 ≤
        (∫ y, |kappa y|) *
          ∫ y, |kappa y| * ‖X ((-y) +ᵥ omega)‖ ^ 2 := by
    have hright := hprod.prod_right_ae
    filter_upwards [hright] with omega homega
    have hweighted : Integrable
        (fun y => |kappa y| * ‖X ((-y) +ᵥ omega)‖) volume := by
      have hdom' : Integrable (fun y => (1 / 2 : ℝ) *
          (|kappa y| * ‖X ((-y) +ᵥ omega)‖ ^ 2 + |kappa y|)) volume :=
        (homega.add hkappaInt.abs).const_mul _
      refine Integrable.mono' hdom' ?_ ?_
      · exact (hkappa.abs.stronglyMeasurable.mul
          (((hXm.comp_measurable
            (measurable_vadd.comp
              (measurable_id.prodMk measurable_const))).comp_measurable
              measurable_neg).norm)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun y => ?_
        have hk0 := abs_nonneg (kappa y)
        have hn := norm_nonneg (X ((-y) +ᵥ omega))
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk0 hn)]
        nlinarith [sq_nonneg (‖X ((-y) +ᵥ omega)‖ - 1)]
    have hnorm : ‖representativeMollify kappa X omega‖ ≤
        ∫ y, |kappa y| * ‖X ((-y) +ᵥ omega)‖ := by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [norm_smul, Real.norm_eq_abs]
    have hjensen := sq_weighted_integral_le
      (nu := (volume : Measure (Vec d)))
      (g := fun y => ‖X ((-y) +ᵥ omega)‖)
      (fun y => abs_nonneg (kappa y)) hkappaInt.abs hweighted homega
    calc
      ‖representativeMollify kappa X omega‖ ^ 2 ≤
          (∫ y, |kappa y| * ‖X ((-y) +ᵥ omega)‖) ^ 2 := by
        nlinarith [norm_nonneg (representativeMollify kappa X omega)]
      _ ≤ _ := hjensen
  have hsm := stronglyMeasurable_representativeMollify hkappa hXm
  refine (memLp_two_iff_integrable_sq_norm hsm.aestronglyMeasurable).2 ?_
  refine Integrable.mono' hdom (hsm.norm.pow 2).aestronglyMeasurable ?_
  filter_upwards [hpoint] with omega homega
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact homega

/-- The spatial gradient representative of a mollified scalar field. -/
def representativeMollifyGrad {d : ℕ}
    (kappa : Vec d → ℝ) (phi : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    HilbertVec d :=
  HilbertVec.ofVec fun i =>
    representativeMollify (Stationary.kernelDeriv kappa i) phi omega

@[simp] theorem representativeMollifyGrad_toVec {d : ℕ}
    (kappa : Vec d → ℝ) (phi : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (i : Fin d) :
    (representativeMollifyGrad kappa phi omega).toVec i =
      representativeMollify (Stationary.kernelDeriv kappa i) phi omega := rfl

/-- The representative gradient is strongly measurable. -/
theorem stronglyMeasurable_representativeMollifyGrad {d : ℕ}
    {kappa : Vec d → ℝ} (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    {phi : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ} (hphim : StronglyMeasurable phi) :
    StronglyMeasurable (representativeMollifyGrad kappa phi) := by
  have hcoord : ∀ i : Fin d, StronglyMeasurable
      (representativeMollify (Stationary.kernelDeriv kappa i) phi) :=
    fun i => stronglyMeasurable_representativeMollify
      (Stationary.continuous_kernelDeriv hkappa i) hphim
  have hvec : Measurable fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      (fun i => representativeMollify
        (Stationary.kernelDeriv kappa i) phi omega : Vec d) :=
    measurable_pi_lambda fun i => (hcoord i).measurable
  exact ((HilbertVec.continuousLinearEquivVec d).symm.continuous)
    |>.comp_stronglyMeasurable hvec.stronglyMeasurable

/-- The representative gradient remains in stationary vector `L²`. -/
theorem memLp_two_representativeMollifyGrad {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    {phi : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ} (hphim : StronglyMeasurable phi)
    (hphi : MemLp phi 2 M.P.toMeasure) :
    MemLp (representativeMollifyGrad kappa phi) 2 M.P.toMeasure := by
  have hcoord : ∀ i : Fin d, MemLp
      (representativeMollify (Stationary.kernelDeriv kappa i) phi)
      2 M.P.toMeasure := fun i =>
    memLp_two_representativeMollify M
      (Stationary.continuous_kernelDeriv hkappa i)
      ((Stationary.continuous_kernelDeriv hkappa i)
        |>.integrable_of_hasCompactSupport
          (Stationary.hasCompactSupport_kernelDeriv hcompact i))
      hphim hphi
  have hmeas := stronglyMeasurable_representativeMollifyGrad hkappa hphim
  refine (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).2 ?_
  have hsum : Integrable
      (fun omega => ∑ i : Fin d,
        representativeMollify (Stationary.kernelDeriv kappa i) phi omega ^ 2)
      M.P.toMeasure :=
    integrable_finset_sum _ fun i _ =>
      (memLp_two_iff_integrable_sq_norm (hcoord i).aestronglyMeasurable).1
        (hcoord i) |>.congr (Filter.Eventually.of_forall fun omega => by
          show ‖representativeMollify
            (Stationary.kernelDeriv kappa i) phi omega‖ ^ 2 =
              representativeMollify
                (Stationary.kernelDeriv kappa i) phi omega ^ 2
          rw [Real.norm_eq_abs, sq_abs])
  refine hsum.congr (Filter.Eventually.of_forall fun omega => ?_)
  show (∑ i : Fin d,
      representativeMollify (Stationary.kernelDeriv kappa i) phi omega ^ 2) =
    ‖representativeMollifyGrad kappa phi omega‖ ^ 2
  rw [HilbertVec.norm_sq_eq_sum_sq]
  rfl

private theorem coeFn_koopman_toLp {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E} (hX : MemLp X 2 M.P.toMeasure) (x : Vec d) :
    letI := potentialSequenceVAddInvariant M
    ∀ᵐ omega ∂M.P.toMeasure,
      (Stationary.koopman (mu := M.P.toMeasure) x (hX.toLp X)) omega =
        X (x +ᵥ omega) := by
  letI := potentialSequenceVAddInvariant M
  have hshift : ∀ᵐ omega ∂M.P.toMeasure,
      (hX.toLp X) (x +ᵥ omega) = X (x +ᵥ omega) :=
    (Stationary.measurePreserving_const_vadd
      (mu := M.P.toMeasure) x).quasiMeasurePreserving.ae hX.coeFn_toLp
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (E := E) (p := 2) (hX.toLp X)
      (Stationary.measurePreserving_const_vadd
        (mu := M.P.toMeasure) x), hshift] with omega h1 h2
  exact h1.trans h2

private theorem integrable_prod_weighted_inner_representativeTranslate
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hkappaInt : Integrable kappa volume)
    {X G : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 M.P.toMeasure) (hGm : StronglyMeasurable G)
    (hG : MemLp G 2 M.P.toMeasure) :
    Integrable
      (fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
        kappa q.2 * inner ℝ (X ((-q.2) +ᵥ q.1)) (G q.1))
      (M.P.toMeasure.prod volume) := by
  have hshift : Measurable fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
      (-q.2) +ᵥ q.1 :=
    measurable_vadd.comp (measurable_snd.neg.prodMk measurable_fst)
  have hXsq : Integrable (fun omega => ‖X omega‖ ^ 2) M.P.toMeasure :=
    (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX
  have hGsq : Integrable (fun omega => ‖G omega‖ ^ 2) M.P.toMeasure :=
    (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).1 hG
  have hjoint : StronglyMeasurable fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
      kappa q.2 * inner ℝ (X ((-q.2) +ᵥ q.1)) (G q.1) :=
    ((hkappa.measurable.comp measurable_snd).stronglyMeasurable).mul
      ((hXm.comp_measurable hshift).inner
        (hGm.comp_measurable measurable_fst))
  have h1 : Integrable
      (fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
        |kappa q.2| * ‖X ((-q.2) +ᵥ q.1)‖ ^ 2)
      (M.P.toMeasure.prod volume) :=
    integrable_prod_weighted_representativeTranslate M
      hkappa.abs hkappaInt.abs (hXm.norm.pow 2) hXsq
  have h2 : Integrable
      (fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d => ‖G q.1‖ ^ 2 * |kappa q.2|)
      (M.P.toMeasure.prod volume) := hGsq.mul_prod hkappaInt.abs
  refine Integrable.mono' ((h1.add h2).const_mul (2⁻¹ : ℝ))
    hjoint.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun q => ?_
  have hcs : |inner ℝ (X ((-q.2) +ᵥ q.1)) (G q.1)| ≤
      ‖X ((-q.2) +ᵥ q.1)‖ * ‖G q.1‖ :=
    abs_real_inner_le_norm _ _
  have hk0 : 0 ≤ |kappa q.2| := abs_nonneg _
  have hstep := mul_le_mul_of_nonneg_left hcs hk0
  have hyoung : ‖X ((-q.2) +ᵥ q.1)‖ * ‖G q.1‖ ≤
      2⁻¹ * (‖X ((-q.2) +ᵥ q.1)‖ ^ 2 + ‖G q.1‖ ^ 2) := by
    nlinarith [sq_nonneg (‖X ((-q.2) +ᵥ q.1)‖ - ‖G q.1‖)]
  have hfinal : |kappa q.2| *
      (‖X ((-q.2) +ᵥ q.1)‖ * ‖G q.1‖) ≤
      2⁻¹ * (|kappa q.2| * ‖X ((-q.2) +ᵥ q.1)‖ ^ 2 +
        ‖G q.1‖ ^ 2 * |kappa q.2|) := by
    have := mul_le_mul_of_nonneg_left hyoung hk0
    nlinarith
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul]
  linarith

private theorem integral_inner_representativeMollify {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hkappaInt : Integrable kappa volume)
    {X G : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 M.P.toMeasure) (hGm : StronglyMeasurable G)
    (hG : MemLp G 2 M.P.toMeasure) :
    ∫ omega, inner ℝ (representativeMollify kappa X omega) (G omega)
        ∂M.P.toMeasure =
      ∫ y, kappa y *
        ∫ omega, inner ℝ (X ((-y) +ᵥ omega)) (G omega)
          ∂M.P.toMeasure := by
  have hprod := integrable_prod_weighted_inner_representativeTranslate M
    hkappa hkappaInt hXm hX hGm hG
  have hpoint : ∀ᵐ omega ∂M.P.toMeasure,
      inner ℝ (representativeMollify kappa X omega) (G omega) =
        ∫ y, kappa y * inner ℝ (X ((-y) +ᵥ omega)) (G omega) := by
    have hscalar : Integrable (fun omega => ‖X omega‖) M.P.toMeasure :=
      (hX.integrable (by norm_num)).norm
    have hweighted :=
      (integrable_prod_weighted_representativeTranslate M
        hkappa.abs hkappaInt.abs (hXm.norm) hscalar).prod_right_ae
    filter_upwards [hweighted] with omega homega
    have hintegrand : Integrable
        (fun y => kappa y • X ((-y) +ᵥ omega)) volume := by
      refine Integrable.mono' homega ?_ (Filter.Eventually.of_forall fun y => ?_)
      · exact (hkappa.stronglyMeasurable.smul
          (((hXm.comp_measurable
            (measurable_vadd.comp
              (measurable_id.prodMk measurable_const))).comp_measurable
                measurable_neg))).aestronglyMeasurable
      · simp only [norm_smul, Real.norm_eq_abs]
        exact le_rfl
    have hcomm := ContinuousLinearMap.integral_comp_comm
      (innerSL ℝ (G omega)) hintegrand
    have hleft : (innerSL ℝ (G omega))
        (representativeMollify kappa X omega) =
          inner ℝ (representativeMollify kappa X omega) (G omega) := by
      rw [innerSL_apply_apply, real_inner_comm]
    rw [← hleft, representativeMollify, ← hcomm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change (innerSL ℝ (G omega))
        (kappa y • X ((-y) +ᵥ omega)) =
      kappa y * inner ℝ (X ((-y) +ᵥ omega)) (G omega)
    rw [innerSL_apply_apply, real_inner_smul_right, real_inner_comm]
  rw [integral_congr_ae hpoint, integral_integral_swap hprod]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun y => integral_const_mul _ _)

/-- The samplewise representative mollifier realizes exactly the existing
Hilbert-space mollifier. -/
theorem toLp_representativeMollify_eq_mollifyL2 {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa)
    {X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 M.P.toMeasure)
    (hXcont : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z (hX.toLp X))) :
    letI := potentialSequenceVAddInvariant M
    (memLp_two_representativeMollify M hkappa
      (hkappa.integrable_of_hasCompactSupport hcompact) hXm hX).toLp
        (representativeMollify kappa X) =
      Stationary.mollifyL2 (mu := M.P.toMeasure) kappa (hX.toLp X) := by
  letI := potentialSequenceVAddInvariant M
  apply ext_inner_right ℝ
  intro G
  classical
  let G0 : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E := (Lp.aestronglyMeasurable G).mk G
  have hGm : StronglyMeasurable G0 :=
    (Lp.aestronglyMeasurable G).stronglyMeasurable_mk
  have hGae : (G : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E) =ᵐ[M.P.toMeasure] G0 :=
    (Lp.aestronglyMeasurable G).ae_eq_mk
  have hGL : MemLp G0 2 M.P.toMeasure := (Lp.memLp G).ae_eq hGae
  have hGtoLp : hGL.toLp G0 = G := by
    rw [MemLp.toLp_congr hGL (Lp.memLp G) hGae.symm, Lp.toLp_coeFn]
  rw [← hGtoLp, MeasureTheory.L2.inner_def]
  have hcoe :
      ∫ omega,
          inner ℝ
            ((memLp_two_representativeMollify M hkappa
              (hkappa.integrable_of_hasCompactSupport hcompact) hXm hX).toLp
                (representativeMollify kappa X) omega)
            ((hGL.toLp G0) omega) ∂M.P.toMeasure =
        ∫ omega, inner ℝ (representativeMollify kappa X omega) (G0 omega)
          ∂M.P.toMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_two_representativeMollify M hkappa
        (hkappa.integrable_of_hasCompactSupport hcompact) hXm hX).coeFn_toLp,
      hGL.coeFn_toLp] with omega h1 h2
    rw [h1, h2]
  rw [hcoe, integral_inner_representativeMollify M hkappa
    (hkappa.integrable_of_hasCompactSupport hcompact) hXm hX hGm hGL]
  have hkoop : ∀ y : Vec d,
      inner ℝ
          (Stationary.koopman (mu := M.P.toMeasure) (-y) (hX.toLp X))
          (hGL.toLp G0) =
        ∫ omega, inner ℝ (X ((-y) +ᵥ omega)) (G0 omega)
          ∂M.P.toMeasure := by
    intro y
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_koopman_toLp M hX (-y), hGL.coeFn_toLp]
      with omega h1 h2
    rw [h1, h2]
  rw [Stationary.mollifyL2]
  have hint :=
    Stationary.integrable_mollifyL2_integrand_of_continuous_koopmanOrbit
      (mu := M.P.toMeasure) hkappa hcompact (hX.toLp X) hXcont
  have hcomm := ContinuousLinearMap.integral_comp_comm
    (innerSL ℝ (hGL.toLp G0)) hint
  calc
    ∫ y, kappa y *
        ∫ omega, inner ℝ (X ((-y) +ᵥ omega)) (G0 omega)
          ∂M.P.toMeasure =
        ∫ y, (innerSL ℝ (hGL.toLp G0))
          (kappa y • Stationary.koopman
          (mu := M.P.toMeasure) (-y) (hX.toLp X)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      change kappa y *
          ∫ omega, inner ℝ (X ((-y) +ᵥ omega)) (G0 omega)
            ∂M.P.toMeasure =
        (innerSL ℝ (hGL.toLp G0))
          (kappa y • Stationary.koopman
            (mu := M.P.toMeasure) (-y) (hX.toLp X))
      rw [innerSL_apply_apply, real_inner_smul_right, real_inner_comm, hkoop]
    _ = (innerSL ℝ (hGL.toLp G0))
        (∫ y, kappa y • Stationary.koopman
          (mu := M.P.toMeasure) (-y) (hX.toLp X)) := hcomm
    _ = inner ℝ
        (∫ y, kappa y • Stationary.koopman
          (mu := M.P.toMeasure) (-y) (hX.toLp X))
        (hGL.toLp G0) := by rw [innerSL_apply_apply, real_inner_comm]

/-- A coordinate representative of a Hilbert-valued random field. -/
def representativeCoord {d : ℕ}
    (F : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d) (i : Fin d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  (F omega).toVec i

theorem stronglyMeasurable_representativeCoord {d : ℕ}
    {F : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d} (hFm : StronglyMeasurable F)
    (i : Fin d) : StronglyMeasurable (representativeCoord F i) :=
  (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d => ℝ) i).continuous
    |>.comp_stronglyMeasurable hFm

theorem memLp_representativeCoord {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {F : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d} (hFm : StronglyMeasurable F)
    (hF : MemLp F 2 M.P.toMeasure) (i : Fin d) :
    MemLp (representativeCoord F i) 2 M.P.toMeasure := by
  refine MemLp.mono' hF.norm
    (stronglyMeasurable_representativeCoord hFm i).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun omega => ?_
  simpa [representativeCoord, Real.norm_eq_abs] using
    HilbertVec.abs_apply_le_norm (F omega) i

/-- Coordinate projection of a vector `L²` class is computed by the
coordinate representative. -/
theorem vectorL2Coord_toLp_representative {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {F : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d} (hFm : StronglyMeasurable F)
    (hF : MemLp F 2 M.P.toMeasure) (i : Fin d) :
    Stationary.vectorL2Coord (mu := M.P.toMeasure) i (hF.toLp F) =
      (memLp_representativeCoord M hFm hF i).toLp
        (representativeCoord F i) := by
  refine Lp.ext ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d => ℝ) i)
      (hF.toLp F), hF.coeFn_toLp,
    (memLp_representativeCoord M hFm hF i).coeFn_toLp]
    with omega h1 h2 h3
  rw [h3]
  refine h1.trans ?_
  rw [h2]
  rfl

/-- Directional derivative of a representative mollification with arbitrary
complete value space. -/
theorem fderiv_realize_representativeMollify_apply {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    {X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E} {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    (hloc : LocallyIntegrable (realize X omega) volume)
    (x : Vec d) (i : Fin d) :
    fderiv ℝ (realize (representativeMollify kappa X) omega) x
        (basisVec i) =
      realize (representativeMollify (Stationary.kernelDeriv kappa i) X)
        omega x := by
  rw [realize_representativeMollify, realize_representativeMollify]
  exact Stationary.fderiv_convolution_apply hcompact hkappa hloc x i

/-- Almost every realization of a representative mollification is smooth,
also for vector-valued representatives. -/
theorem ae_contDiff_realize_representativeMollify {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    {X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → E} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 M.P.toMeasure) :
    ∀ᵐ omega ∂M.P.toMeasure,
      ContDiff ℝ (⊤ : ℕ∞)
        (realize (representativeMollify kappa X) omega) := by
  filter_upwards [ae_locallyIntegrable_realize M hXm hX] with omega hloc
  rw [realize_representativeMollify]
  exact hcompact.contDiff_convolution_left _ hkappa hloc

/-- Directional differentiation of the smooth realized representative puts
the derivative on the mollifier. -/
theorem fderiv_realize_representativeMollify {d : ℕ}
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    {phi : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ} {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    (hloc : LocallyIntegrable (realize phi omega) volume)
    (x : Vec d) (i : Fin d) :
    fderiv ℝ (realize (representativeMollify kappa phi) omega) x
        (basisVec i) =
      (realize (representativeMollifyGrad kappa phi) omega x).toVec i := by
  change fderiv ℝ (realize (representativeMollify kappa phi) omega) x
      (basisVec i) =
    realize (representativeMollify (Stationary.kernelDeriv kappa i) phi)
      omega x
  rw [realize_representativeMollify, realize_representativeMollify]
  exact Stationary.fderiv_convolution_apply hcompact hkappa hloc x i

/-- A mollified stationary representative has almost surely a smooth spatial
primitive whose gradient is the displayed stationary representative. -/
theorem ae_smooth_primitive_representativeMollify {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    {phi : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ} (hphim : StronglyMeasurable phi)
    (hphi : MemLp phi 2 M.P.toMeasure) :
    ∀ᵐ omega ∂M.P.toMeasure,
      ContDiff ℝ (⊤ : ℕ∞)
          (realize (representativeMollify kappa phi) omega) ∧
        ∀ (x : Vec d) (i : Fin d),
          fderiv ℝ (realize (representativeMollify kappa phi) omega) x
              (basisVec i) =
            (realize (representativeMollifyGrad kappa phi) omega x).toVec i := by
  filter_upwards [ae_locallyIntegrable_realize M hphim hphi] with omega hloc
  refine ⟨?_, fun x i =>
    fderiv_realize_representativeMollify hcompact hkappa hloc x i⟩
  rw [realize_representativeMollify]
  exact hcompact.contDiff_convolution_left _ hkappa hloc

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
