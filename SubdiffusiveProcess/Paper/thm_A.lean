module

public import SubdiffusiveProcess.Paper.mfd_convergence
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.Paper.lim_brownian_law
public import SubdiffusiveProcess.Paper.lim_nonbrownian
public import SubdiffusiveProcess.Paper.lim_paths
public import SubdiffusiveProcess.Paper.lim_measure
public import SubdiffusiveProcess.Paper.lim_invariance
public import SubdiffusiveProcess.Paper.lim_transition_domination
public import SubdiffusiveProcess.Paper.lim_nongaussian
public import Mathlib.Probability.Distributions.Gaussian.Basic

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open MarkovProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The exit time of `Z - Z_0` from a ball is a measurable function of the path. -/
theorem aux_thm_A_exitTime_centered_measurable {d : ℕ} (r : ℝ) :
    Measurable (fun w : DiffusionPath d ↦
      ContinuousPath.exitTime (Metric.ball (w 0) r) w) := by
  let shift : DiffusionPath d → DiffusionPath d := fun w ↦ w - ContinuousMap.const _ (w 0)
  have hshift : Continuous shift := by
    refine continuous_id.sub ?_
    exact ContinuousMap.continuous_const'.comp (continuous_eval_const (0 : ℝ≥0))
  have heq : (fun w : DiffusionPath d ↦ ContinuousPath.exitTime (Metric.ball (w 0) r) w) =
      (ContinuousPath.exitTime (Metric.ball (0 : SpatialCoordinates d) r)) ∘ shift := by
    funext w
    simp only [Function.comp, ContinuousPath.exitTime, shift, ContinuousMap.sub_apply,
      ContinuousMap.const_apply, Metric.mem_ball, dist_eq_norm, sub_zero]
  rw [heq]
  exact (ContinuousPath.measurable_exitTime _ Metric.isOpen_ball).comp hshift.measurable

/-- The annealed law `E[K^ω_x]` is a probability measure. -/
theorem aux_thm_A_bind_isProb {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (law : Measure (BilateralField d)) [IsProbabilityMeasure law]
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (x : SpatialCoordinates d) :
    IsProbabilityMeasure (law.bind (fun omega ↦ K (omega, x))) := by
  constructor
  have hm : Measurable (fun omega : BilateralField d ↦ K (omega, x)) :=
    K.measurable.comp measurable_prodMk_right
  rw [Measure.bind_apply MeasurableSet.univ hm.aemeasurable]
  simp [measure_univ]

/-- Integrals against the annealed law are iterated integrals. -/
theorem aux_thm_A_integral_bind {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (law : Measure (BilateralField d)) [IsProbabilityMeasure law]
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (x : SpatialCoordinates d)
    (G : BoundedContinuousFunction (DiffusionPath d) ℝ) :
    ∫ w, G w ∂(law.bind (fun omega ↦ K (omega, x))) =
      ∫ omega, (∫ w, G w ∂(K (omega, x))) ∂law := by
  let kx : Kernel (BilateralField d) (DiffusionPath d) :=
    K.comap (fun omega ↦ (omega, x)) measurable_prodMk_right
  have hbind : law.bind (fun omega ↦ K (omega, x)) = (kx ∘ₖ Kernel.const Unit law) () := by
    rw [Kernel.comp_apply, Kernel.const_apply]
    rfl
  have : IsProbabilityMeasure (law.bind (fun omega ↦ K (omega, x))) :=
    aux_thm_A_bind_isProb law K hK x
  have hint : Integrable (fun w ↦ G w) ((kx ∘ₖ Kernel.const Unit law) ()) := by
    rw [← hbind]
    exact G.integrable _
  rw [hbind, Kernel.integral_comp hint, Kernel.const_apply]
  rfl

/-- An almost sure statement for the annealed law holds, almost surely, for the quenched laws. -/
theorem aux_thm_A_ae_of_bind {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (law : Measure (BilateralField d))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (x : SpatialCoordinates d) (p : DiffusionPath d → Prop)
    (h : ∀ᵐ w ∂(law.bind (fun omega ↦ K (omega, x))), p w) :
    ∀ᵐ omega ∂law, ∀ᵐ w ∂(K (omega, x)), p w := by
  have hm : Measurable (fun omega : BilateralField d ↦ K (omega, x)) :=
    K.measurable.comp measurable_prodMk_right
  rw [ae_iff] at h
  obtain ⟨T, hsub, hTm, hT0⟩ := exists_measurable_superset_of_null h
  rw [Measure.bind_apply hTm hm.aemeasurable] at hT0
  have h0 := (lintegral_eq_zero_iff (Kernel.measurable_coe K hTm |>.comp
    measurable_prodMk_right)).1 hT0
  filter_upwards [h0] with omega homega
  rw [ae_iff]
  exact measure_mono_null hsub homega

/-- Almost sure locally uniform Lévy–Prokhorov convergence at `x` gives convergence of the
annealed integrals of bounded continuous path functionals. -/
theorem aux_thm_A_annealed_tendsto {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (law : Measure (BilateralField d)) [IsProbabilityMeasure law]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (x : SpatialCoordinates d)
    (hconv : ∀ᵐ omega ∂law,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ y ∈ B,
          pathLevyProkhorovDist
            (jointPathProbabilityMeasure (KN N) (hKN N) omega y)
            (jointPathProbabilityMeasure K hK omega y) < epsilon)
    (G : BoundedContinuousFunction (DiffusionPath d) ℝ) :
    Tendsto (fun n ↦ ∫ omega, (∫ w, G w ∂(KN n (omega, x))) ∂law) atTop
      (𝓝 (∫ omega, (∫ w, G w ∂(K (omega, x))) ∂law)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ ‖G‖) (fun n ↦ ?_)
    (integrable_const _) (fun n ↦ ?_) ?_
  · exact ((G.continuous.stronglyMeasurable).integral_kernel (κ := (KN n).comap
      (fun omega ↦ (omega, x)) measurable_prodMk_right)).aestronglyMeasurable
  · refine Eventually.of_forall fun omega ↦ ?_
    have := (hKN n).isProbabilityMeasure (omega, x)
    exact (norm_integral_le_of_norm_le_const (Eventually.of_forall fun w ↦ G.norm_coe_le_norm w)).trans
      (by simp)
  · filter_upwards [hconv] with omega homega
    have hlp : ∀ ε : ℝ, 0 < ε → ∃ J0 : ℕ, ∀ j : ℕ, J0 ≤ j →
        pathLevyProkhorovDist (jointPathProbabilityMeasure (KN j) (hKN j) omega x)
          (jointPathProbabilityMeasure K hK omega x) < ε := by
      intro ε hε
      obtain ⟨N0, hN0⟩ := homega {x} isCompact_singleton ε hε
      exact ⟨N0, fun j hj ↦ hN0 j hj x rfl⟩
    have ht := aux_in_stopped_passage_tendsto_of_pathLP hlp
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 ht) G

/-- `P ↦ ∫ G dP` is measurable on probability measures (for the Giry σ-algebra). -/
theorem aux_thm_A_measurable_integral_pm {d : ℕ}
    (G : BoundedContinuousFunction (DiffusionPath d) ℝ) :
    Measurable (fun P : ProbabilityMeasure (DiffusionPath d) ↦
      ∫ w, G w ∂(P : Measure (DiffusionPath d))) := by
  have hG : Measurable (fun w : DiffusionPath d ↦ G w) := G.continuous.measurable
  have hpos : Measurable (fun P : ProbabilityMeasure (DiffusionPath d) ↦
      ∫⁻ w, ENNReal.ofReal (G w) ∂(P : Measure (DiffusionPath d))) :=
    (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hG)).comp
      measurable_subtype_coe
  have hneg : Measurable (fun P : ProbabilityMeasure (DiffusionPath d) ↦
      ∫⁻ w, ENNReal.ofReal (-G w) ∂(P : Measure (DiffusionPath d))) :=
    (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hG.neg)).comp
      measurable_subtype_coe
  have heq : (fun P : ProbabilityMeasure (DiffusionPath d) ↦
      ∫ w, G w ∂(P : Measure (DiffusionPath d))) = fun P : ProbabilityMeasure (DiffusionPath d) ↦
      (∫⁻ w, ENNReal.ofReal (G w) ∂(P : Measure (DiffusionPath d))).toReal -
        (∫⁻ w, ENNReal.ofReal (-G w) ∂(P : Measure (DiffusionPath d))).toReal := by
    funext P
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (G.integrable _)
  rw [heq]
  exact hpos.ennreal_toReal.sub hneg.ennreal_toReal

/-- The quenched law at `x` is a measurable function of the environment. -/
theorem aux_thm_A_measurable_quenched {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (x : SpatialCoordinates d) :
    Measurable (fun omega : BilateralField d ↦ jointPathProbabilityMeasure K hK omega x) := by
  unfold jointPathProbabilityMeasure
  exact (K.measurable.comp measurable_prodMk_right).subtype_mk

/-- Strict decay of the conductances gives the clock scaling `T_m/T_ℓ ≥ C'⁻¹ 3^{(2+η')(m-ℓ)}`. -/
theorem aux_thm_A_clock (a : ℕ → ℝ) (hpos : ∀ n, 0 < a n) (C eta C' eta' : ℝ)
    (hC : 0 < C) (hCC : C ≤ C') (heta : eta' ≤ eta)
    (hdec : ∀ l m : ℕ, l ≤ m → a m / a l ≤ C * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (l : ℝ))))) :
    ∀ l m : ℕ, l ≤ m →
      C'⁻¹ * (3 : ℝ) ^ ((2 + eta') * ((m : ℝ) - (l : ℝ))) ≤
        ((3 : ℝ) ^ (2 * m) / a m) / ((3 : ℝ) ^ (2 * l) / a l) := by
  intro l m hlm
  set s : ℝ := (m : ℝ) - (l : ℝ) with hs
  have hs0 : 0 ≤ s := by rw [hs, sub_nonneg]; exact_mod_cast hlm
  have ha := hdec l m hlm
  have hal := hpos l
  have ham := hpos m
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hpow : ((3 : ℝ) ^ (2 * m) / a m) / ((3 : ℝ) ^ (2 * l) / a l) =
      (3 : ℝ) ^ ((2 : ℝ) * s) * (a l / a m) := by
    have e1 : (3 : ℝ) ^ (2 * m) = (3 : ℝ) ^ ((2 : ℝ) * (m : ℝ)) := by
      rw [← Real.rpow_natCast]; push_cast; ring_nf
    have e2 : (3 : ℝ) ^ (2 * l) = (3 : ℝ) ^ ((2 : ℝ) * (l : ℝ)) := by
      rw [← Real.rpow_natCast]; push_cast; ring_nf
    have e3 : (3 : ℝ) ^ ((2 : ℝ) * s) = (3 : ℝ) ^ ((2 : ℝ) * (m : ℝ)) / (3 : ℝ) ^ ((2 : ℝ) * (l : ℝ)) := by
      rw [← Real.rpow_sub h3, hs]; ring_nf
    rw [e1, e2, e3]
    field_simp
  rw [hpow]
  have hinv : C⁻¹ * (3 : ℝ) ^ (eta * s) ≤ a l / a m := by
    have hq : 0 < C * (3 : ℝ) ^ (-(eta * s)) := mul_pos hC (Real.rpow_pos_of_pos h3 _)
    have h1 : a m / a l ≤ C * (3 : ℝ) ^ (-(eta * s)) := ha
    have h2 : (C * (3 : ℝ) ^ (-(eta * s)))⁻¹ ≤ (a m / a l)⁻¹ :=
      inv_anti₀ (div_pos ham hal) h1
    rw [inv_div] at h2
    calc C⁻¹ * (3 : ℝ) ^ (eta * s) = (C * (3 : ℝ) ^ (-(eta * s)))⁻¹ := by
          rw [mul_inv, Real.rpow_neg h3.le, inv_inv]
      _ ≤ a l / a m := h2
  have hC' : 0 < C' := lt_of_lt_of_le hC hCC
  calc C'⁻¹ * (3 : ℝ) ^ ((2 + eta') * s)
      ≤ C⁻¹ * (3 : ℝ) ^ ((2 + eta) * s) := by
        apply mul_le_mul (inv_anti₀ hC hCC)
          (Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (mul_le_mul_of_nonneg_right (by linarith) hs0))
          (Real.rpow_pos_of_pos h3 _).le (inv_pos.mpr hC).le
    _ = (3 : ℝ) ^ ((2 : ℝ) * s) * (C⁻¹ * (3 : ℝ) ^ (eta * s)) := by
        rw [show (2 + eta) * s = (2 : ℝ) * s + eta * s by ring, Real.rpow_add h3]; ring
    _ ≤ (3 : ℝ) ^ ((2 : ℝ) * s) * (a l / a m) :=
        mul_le_mul_of_nonneg_left hinv (Real.rpow_pos_of_pos h3 _).le

/-- **Theorem A** (`t.A`): convergence of the
process (the conclusion of `mfd_convergence`, with its carried inputs) together with the
heat-kernel-free properties of the limit, stated for the SAME witnesses `H, PN, P, KN, K`:
(ii) the limiting measures `M = lim M_N`, `μ = e^H M` (local weak limits, locally finite,
nonatomic, full support, singular; `M` non-deterministic, stationary, mean Lebesgue) and invariance
of `μ` for the limiting process; (iii) strict clock scaling `T_m/T_ℓ ≥ C⁻¹ 3^{(2+η)(m-ℓ)}`,
annealed small-cube exit bounds, mutual singularity with Brownian laws and their mixtures, the
pointwise Hölder upper bound `1/(2+η)` (`η = τ²/log 3` in `d = 2`); (iv) positive-time transition
laws absolutely continuous w.r.t. `μ` and non-Gaussian.  Formal scope as in the `lim_*` nodes
(cutoff family; the cutoff-family convention). -/
theorem thm_A
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)
    (hlife : ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
        (∃ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
          (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
          (∀ N, IsMarkovKernel (KN N)) ∧ in_crossing M H PN KN) →
        ∃ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
          (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
          (∀ N, IsMarkovKernel (KN N)) ∧ in_crossing M H PN KN ∧
            aux_cutoff_lifetime_package_LocalInput M H KN) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg),
        0 < M.delta → M.delta ≤ delta0 →
        let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
            C(SpatialCoordinates d, ℝ)) :=
          ⟨fun g ↦ g.1.1, continuous_subtype_val.fst⟩
        let nu := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).map forget
        let law := (commonScaleLaw d nu).toMeasure
        ∃ C eta : ℝ, 1 ≤ C ∧ 0 < eta ∧
        (d = 2 → eta = _root_.SubdiffusiveProcess.Model.tauSq M.P / Real.log 3) ∧
        (∀ l m : ℕ, l ≤ m →
          C⁻¹ * (3 : ℝ) ^ ((2 + eta) * ((m : ℝ) - (l : ℝ))) ≤
            ((3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m) /
              ((3 : ℝ) ^ (2 * l) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M l)) ∧
        ∃ H : BilateralField d → C(SpatialCoordinates d, ℝ), Measurable H ∧
        ∃ PN : ℕ → BilateralField d →
            SubMarkovKernelSemigroup (SpatialCoordinates d),
        ∃ hPN : ∀ N omega, (PN N omega).IsConservative,
        ∃ P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d),
        ∃ hP : ∀ omega, (P omega).IsConservative,
        ∃ KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d),
        ∃ hKN : ∀ N, IsMarkovKernel (KN N),
        ∃ K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d),
        ∃ hK : IsMarkovKernel K,
          (∀ᵐ omega ∂law,
            Tendsto (infraredPartialSum omega) atTop (nhds (H omega)) ∧
            (∀ N, ∃ D :
                SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
                  (SpatialCoordinates d),
              (∀ mu, DenseRange (D.operator mu)) ∧
              SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
                (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D ∧
              ∀ (mu : Semigroup.PositiveShift)
                (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
                (x : SpatialCoordinates d),
                D.solution mu f x =
                  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
                    kernelIntegral (PN N omega (Real.toNNReal t)) f x) ∧
            (∀ N I x,
              (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
                SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x) ∧
            (∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
              SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x) ∧
            Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x) ∧
            (∀ B : Set (SpatialCoordinates d), IsCompact B →
              ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
                ∀ x ∈ B,
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (jointPathProbabilityMeasure K hK omega x) < epsilon) ∧
            (∀ (t : ℝ≥0) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
              Continuous (kernelIntegral (P omega t) f)) ∧
            (∃ mu : Measure (SpatialCoordinates d),
              MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu ∧
              IsLocallyFiniteMeasure mu ∧ NullSingletonClass mu ∧ mu.IsOpenPosMeasure ∧
              SemigroupSymmetric (P omega) mu) ∧
            HasStrongMarkovRestart K omega ∧ HasFiniteMeanExits K omega) ∧
          (∀ (x : SpatialCoordinates d) (F : BoundedContinuousFunction (DiffusionPath d) ℝ),
            Tendsto
              (fun N ↦ ∫ omega,
                (∫ path, F (physicalRescaledPath M N path)
                  ∂(KN 0 (omega, (3 : ℝ) ^ N • x))) ∂law)
              atTop
              (nhds (∫ omega, (∫ path, F path ∂(K (omega, x))) ∂law))) ∧
          -- (ii) the limiting measures `M = lim M_N` and `μ = e^H M`, reversibility's invariance
          (∃ Mlim : BilateralField d → Measure (SpatialCoordinates d), Measurable Mlim ∧
            (∀ᵐ omega ∂law,
              let mu := (Mlim omega).withDensity
                (fun y ↦ ENNReal.ofReal (Real.exp (H omega y)))
              MeasuresConvergeLocally (fun N ↦ chaosCutoff M N omega) (Mlim omega) ∧
              MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu ∧
              IsLocallyFiniteMeasure (Mlim omega) ∧ NullSingletonClass (Mlim omega) ∧
              (Mlim omega).IsOpenPosMeasure ∧ Mlim omega ⟂ₘ volume ∧
              IsLocallyFiniteMeasure mu ∧ NullSingletonClass mu ∧ mu.IsOpenPosMeasure ∧ mu ⟂ₘ volume ∧
              (∀ (t : ℝ≥0) (f : SpatialCoordinates d → ℝ≥0∞), Measurable f →
                ∫⁻ x, (∫⁻ w, f (w t) ∂(K (omega, x))) ∂mu = ∫⁻ x, f x ∂mu) ∧
              -- (iv) positive-time transition laws: absolutely continuous, non-Gaussian
              ∀ (x : SpatialCoordinates d) (t : ℝ≥0), 0 < t →
                (K (omega, x)).map (fun w : DiffusionPath d ↦ w t) ≪ mu ∧
                ¬ IsGaussian ((K (omega, x)).map (fun w : DiffusionPath d ↦ w t))) ∧
            (¬ ∃ m : Measure (SpatialCoordinates d), ∀ᵐ omega ∂law, Mlim omega = m) ∧
            (∀ A : Set (SpatialCoordinates d), MeasurableSet A →
              ∫⁻ omega, Mlim omega A ∂law = volume A) ∧
            ∀ y : SpatialCoordinates d,
              law.map (fun omega ↦ (Mlim omega).map (fun z ↦ z + y)) = law.map Mlim) ∧
          -- (iii) annealed small-cube exits, Brownian singularity, pointwise Hölder bound
          (∀ (x : SpatialCoordinates d) (k : ℕ),
            ∫⁻ omega, (∫⁻ w, ContinuousPath.exitTime
                (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w ∂(K (omega, x))) ∂law ≤
              ENNReal.ofReal (C * (3 : ℝ) ^ (-((2 + eta) * (k : ℝ))))) ∧
          ∀ x : SpatialCoordinates d, ∀ᵐ omega ∂law,
            (∀ Q : Measure (DiffusionPath d), lim_brownian_law Q → K (omega, x) ⟂ₘ Q) ∧
            (∀ (Θ : Type) [MeasurableSpace Θ] (nu' : Measure Θ) [IsProbabilityMeasure nu']
                (kappa : Kernel Θ (DiffusionPath d)), (∀ θ, lim_brownian_law (kappa θ)) →
              K (omega, x) ⟂ₘ nu'.bind kappa) ∧
            ∀ᵐ w ∂(K (omega, x)), ∀ gamma : ℝ, 0 ≤ gamma →
              (fun t : ℝ≥0 ↦ ‖w t - w 0‖) =O[𝓝[>] 0] (fun t : ℝ≥0 ↦ (t : ℝ) ^ gamma) →
              gamma ≤ 1 / (2 + eta) := by
  classical
  obtain ⟨dNB, hdNB, hNB⟩ := lim_nonbrownian hd Jc Pc Xc Sf W Cp
  obtain ⟨dPA, hdPA, hPA⟩ := lim_paths hd Jc Pc Xc Sf W Cp
  obtain ⟨dME, hdME, hME⟩ := lim_measure (d := d) hd
  obtain ⟨dIN, hdIN, hIN⟩ := lim_invariance hd Jc Pc Xc Sf W Cp
  obtain ⟨dTD, hdTD, hTD⟩ := lim_transition_domination hd Jc Pc Xc Sf W Cp
  obtain ⟨dNG, hdNG, hNG⟩ := lim_nongaussian hd Jc Pc Xc Sf W Cp
  have h0pos := aux_mfd_convergence_delta0_pos hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp BD BDQ
    hcontract
  refine ⟨min (aux_mfd_convergence_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp BD BDQ hcontract)
      (min dNB (min dPA (min dME (min dIN (min dTD dNG))))),
    lt_min h0pos (lt_min hdNB (lt_min hdPA (lt_min hdME (lt_min hdIN (lt_min hdTD hdNG))))), ?_⟩
  intro M Rm Sreg It hMpos hMle forget nu law
  have hle0 := hMle.trans (min_le_left _ _)
  have hr := hMle.trans (min_le_right _ _)
  have hleNB : M.delta ≤ dNB := hr.trans (min_le_left _ _)
  have hr2 := hr.trans (min_le_right _ _)
  have hlePA : M.delta ≤ dPA := hr2.trans (min_le_left _ _)
  have hr3 := hr2.trans (min_le_right _ _)
  have hleME : M.delta ≤ dME := hr3.trans (min_le_left _ _)
  have hr4 := hr3.trans (min_le_right _ _)
  have hleIN : M.delta ≤ dIN := hr4.trans (min_le_left _ _)
  have hr5 := hr4.trans (min_le_right _ _)
  have hleTD : M.delta ≤ dTD := hr5.trans (min_le_left _ _)
  have hleNG : M.delta ≤ dNG := hr5.trans (min_le_right _ _)
  -- the witnesses of `mfd_convergence`, built exactly as its proof builds them
  have hle1 : M.delta ≤ Classical.choose (finiteDimensional_cutoff (d := d) hd) := by
    have h := hle0
    unfold aux_mfd_convergence_delta0 at h
    exact h.trans ((min_le_left _ _).trans (min_le_left _ _))
  obtain ⟨H, hH⟩ := exists_infraredCharacterization hd M
  have hFD := (Classical.choose_spec (finiteDimensional_cutoff (d := d) hd)).2 M H hH hle1
  obtain ⟨PN, KN, hKN, hin, hinput⟩ := hlife M H hH hFD
  obtain ⟨P, hP, K, hK, hae, hann⟩ := aux_mfd_convergence_core hd Jc Pc Xc Sf W Cp D hES Step Dbase
    Interp BD BDQ hcontract M Rm Sreg It hMpos hle0 H hH PN KN hKN hin hinput
  obtain ⟨L, hL, hLloc, -⟩ := aux_cutoff_lifetime_package_local M H KN hinput
  have hconv : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ x ∈ B,
          pathLevyProkhorovDist
            (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
            (jointPathProbabilityMeasure K hK omega x) < epsilon := by
    filter_upwards [hae] with omega homega
    exact homega.2.2.2.2.2.1
  -- the per-model constants of the §10 nodes
  obtain ⟨Cnb, enb, hCnb, henb, hd2nb, hdecnb, hNBm⟩ := hNB M Rm Sreg It hleNB
  obtain ⟨Cpa, epa, -, hepa, hd2pa, -, hPAm⟩ := hPA M Rm Sreg It hlePA
  obtain ⟨cp1, -, hPAm1⟩ := hPAm 1 one_pos
  have hNBx := hNBm H hH PN KN hKN hin L hL hLloc
  have hPAx := hPAm1 H hH PN KN hKN hin L hL hLloc
  have : IsProbabilityMeasure law := (chaosSampleLaw M).prop
  -- the annealed limit at a deterministic start
  have hPlim : ∀ x : SpatialCoordinates d,
      ∀ G : BoundedContinuousFunction (DiffusionPath d) ℝ,
        Tendsto (fun n ↦ ∫ omega, (∫ w, G w ∂(KN (id n) (omega, (fun _ : ℕ ↦ x) n))) ∂law)
          atTop (𝓝 (∫ w, G w ∂(law.bind (fun omega ↦ K (omega, x))))) := by
    intro x G
    rw [aux_thm_A_integral_bind law K hK x G]
    exact aux_thm_A_annealed_tendsto law KN hKN K hK x hconv G
  have hKm : ∀ x : SpatialCoordinates d, Measurable (fun omega : BilateralField d ↦ K (omega, x)) :=
    fun x ↦ K.measurable.comp measurable_prodMk_right
  refine ⟨max Cnb 1, min enb epa, le_max_right _ _, lt_min henb hepa, ?_, ?_,
    H, hH.1, PN, hin.2.1, P, hP, KN, hKN, K, hK, hae, hann, ?_, ?_, ?_⟩
  · intro h2
    rw [hd2nb h2, hd2pa h2, min_self]
  · exact aux_thm_A_clock (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M)
      Cnb enb (max Cnb 1) (min enb epa) hCnb (le_max_left _ _) (min_le_left _ _) hdecnb
  · -- (ii) and (iv)
    obtain ⟨Mlim, hMlim, hMae, hnondet, hmean, hstat, -⟩ := hME M H hH hleME
    have hINx := hIN M Rm Sreg It hleIN H hH PN KN hKN hin L hL hLloc K hK hconv
    have hTDx := hTD M Rm Sreg It hleTD H hH PN KN hKN hin L hL hLloc K hK hconv
    have hNGx := hNG M Rm Sreg It hleNG H hH PN KN hKN hin L hL hLloc K hK hconv
    refine ⟨Mlim, hMlim, ?_, hnondet, hmean, hstat⟩
    filter_upwards [hMae, hINx, hTDx, hNGx] with omega h1 h2 h3 h4
    obtain ⟨c1, c2, lf1, na1, op1, s1, lf2, na2, op2, s2⟩ := h1
    have c2' : MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N)
        ((Mlim omega).withDensity (fun y ↦ ENNReal.ofReal (Real.exp (H omega y)))) := by
      simpa only [cutoffSpeedMeasure_eq_weightedChaosCutoff] using c2
    exact ⟨c1, c2', lf1, na1, op1, s1, lf2, na2, op2, s2, h2 _ c2',
      fun x t ht ↦ ⟨h3 _ c2' x t ht, h4 x t ht⟩⟩
  · -- (iii) annealed small-cube exits
    intro x k
    have : IsProbabilityMeasure (law.bind (fun omega ↦ K (omega, x))) :=
      aux_thm_A_bind_isProb law K hK x
    have hex := (hNBx id strictMono_id (fun _ ↦ x) x tendsto_const_nhds
      ⟨law.bind (fun omega ↦ K (omega, x)), inferInstance⟩ (hPlim x)).1 k
    have hex' : ∫⁻ w, ContinuousPath.exitTime (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w
        ∂(law.bind (fun omega ↦ K (omega, x))) ≤
        ENNReal.ofReal (Cnb * (3 : ℝ) ^ (-((2 + enb) * (k : ℝ)))) := hex
    rw [Measure.lintegral_bind (hKm x).aemeasurable
      (aux_thm_A_exitTime_centered_measurable _).aemeasurable] at hex'
    replace hex := hex'
    refine hex.trans (ENNReal.ofReal_le_ofReal ?_)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    apply mul_le_mul (le_max_left _ _) _ (Real.rpow_pos_of_pos (by norm_num) _).le
      (le_trans hCnb.le (le_max_left _ _))
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (2 + min enb epa) * (k : ℝ) ≤ (2 + enb) * (k : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith [min_le_left enb epa]) hk0
    linarith
  · -- (iii) Brownian singularity (one null set for all Brownian laws) and the Hölder bound
    intro x
    have : IsProbabilityMeasure (law.bind (fun omega ↦ K (omega, x))) :=
      aux_thm_A_bind_isProb law K hK x
    have hΦ := aux_thm_A_measurable_quenched K hK x
    have : IsProbabilityMeasure (law.map (fun omega ↦ jointPathProbabilityMeasure K hK omega x)) :=
      inferInstance
    have hrand := (hNBx id strictMono_id (fun _ ↦ x) x tendsto_const_nhds
      ⟨law.bind (fun omega ↦ K (omega, x)), inferInstance⟩ (hPlim x)).2.2.2
      (law.map (fun omega ↦ jointPathProbabilityMeasure K hK omega x)) inferInstance
      (fun G ↦ by
        rw [integral_map hΦ.aemeasurable (aux_thm_A_measurable_integral_pm G).aestronglyMeasurable]
        exact aux_thm_A_annealed_tendsto law KN hKN K hK x hconv G)
    have hsing := ae_of_ae_map hΦ.aemeasurable hrand
    have hhold := (hPAx id strictMono_id (fun _ ↦ x) x tendsto_const_nhds
      ⟨law.bind (fun omega ↦ K (omega, x)), inferInstance⟩ (hPlim x)).2.1
    have hhold' := aux_thm_A_ae_of_bind law K x _ hhold
    filter_upwards [hsing, hhold'] with omega h1 h2
    refine ⟨h1.1, h1.2, ?_⟩
    filter_upwards [h2] with w hw gamma hgamma hO
    exact (hw gamma hgamma hO).trans
      (one_div_le_one_div_of_le (by linarith [lt_min henb hepa]) (by linarith [min_le_right enb epa]))

end SubdiffusiveProcess.Paper
