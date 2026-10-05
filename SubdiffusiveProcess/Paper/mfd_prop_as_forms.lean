module

public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.in_killed_energy
public import SubdiffusiveProcess.Paper.car_variational
public import SubdiffusiveProcess.Paper.cor_as_resolvent
public import SubdiffusiveProcess.Paper.inputs_simultaneous
public import SubdiffusiveProcess.Paper.mfd_convergence
public import SubdiffusiveProcess.Paper.lem_19_trace_completion
public import SubdiffusiveProcess.Paper.lem_19_smooth_density
public import SubdiffusiveProcess.Paper.prop_as_forms
public import SubdiffusiveProcess.Paper.limiting_local_energy
public import SubdiffusiveProcess.Paper.prop_uniform_resolvent
public import SubdiffusiveProcess.Paper.prop_uniform_resolvent_cutoff_oscillation
public import SubdiffusiveProcess.Paper.prop_speed_resolvent
public import SubdiffusiveProcess.Paper.prop_chaos_growth
public import SubdiffusiveProcess.Paper.finiteDimensional_cutoff
public import SubdiffusiveProcess.Paper.cutoff_lifetime_package
public import SubdiffusiveProcess.Section9.CubeTrace
public import SubdiffusiveProcess.Section9.CubeAverages
public import SubdiffusiveProcess.Section9.RationalCubes
public import SubdiffusiveProcess.Sobolev.VolumeResponseOperator
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.DirichletForm.All
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess SubdiffusiveProcess
open Set TopologicalSpace Metric _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped InnerProductSpace ENNReal NNReal LevyProkhorov BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper
/-- The proved geometric cube Poincare inequality, used as a constructor argument. -/
theorem aux_mfd_prop_as_forms_poincare {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube z r hr),
      ‖(v : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) v‖ := by
  have : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩
  exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
    (centeredCube z r hr) (isOpenBoundedConvexDomain_centeredCube z hr)).1

theorem aux_mfd_prop_as_forms_inverse_supply
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
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
          responseForm S a v v ≤ responseForm S a u u) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization M H), M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        (∃ j : ℤ, r = (3 : ℝ) ^ j) →
        (∀ k : Fin d, ∃ q : ℚ, z k = (q : ℝ)) →
      ∃ G : BilateralField d → DomainL2 (centeredCube z r hr) →L[ℝ]
          DomainL2 (centeredCube z r hr),
        Measurable G ∧
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          let Q := centeredCube z r hr;
          let hp := aux_mfd_prop_as_forms_poincare hd z r hr;
          let GN := fun N => volumeResponseOperator (killedResponseSpace hp)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr);
          let EN := fun N (u : DomainL2 Q) =>
            ⨅ v : {v : killedSobolevGraph Q // (v : SobolevData Q).1 = u},
              ((in_killed_energy M H hH omega N z hr
                (v : killedSobolevGraph Q) (v : killedSobolevGraph Q) : ℝ) : EReal);
          Tendsto GN atTop (𝓝 (G omega)) ∧ IsCompactOperator (G omega) ∧
          (∀ x y : DomainL2 Q, inner ℝ (G omega x) y = inner ℝ x (G omega y)) ∧
          (∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G omega x)) ∧ Function.Injective (G omega) ∧
          (∃ F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))),
            (∀ u : DomainL2 Q, F.toClosedForm.energy u = limitFormEnergy (G omega) u) ∧
            _root_.SubdiffusiveProcess.DirichletForm.IsRegular F.toClosedForm ∧ _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal F.toClosedForm) ∧
          (∀ (uN : ℕ → DomainL2 Q) (u : DomainL2 Q),
            (∀ f : DomainL2 Q, Tendsto (fun N => inner ℝ f (uN N)) atTop (𝓝 (inner ℝ f u))) →
            limitFormEnergy (G omega) u ≤ liminf (fun N => EN N (uN N)) atTop) ∧
          (∀ u : DomainL2 Q, ∃ w : ℕ → DomainL2 Q, Tendsto w atTop (𝓝 u) ∧
            limsup (fun N => EN N (w N)) atTop ≤ limitFormEnergy (G omega) u) ∧
          (∀ u : DomainL2 Q, limitFormEnergy (G omega) u ≠ ⊤ →
            ∃ v : CubeFractionalL2 (k := 1) hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder, v.val 0 = u) := by
  classical
  obtain ⟨δl, hδl, hLimit⟩ := limiting_local_energy d hd Jc Pc Xc Sf W Cp D hES
    Step Dbase Interp BD BDQ hcontract
  obtain ⟨δf, hδf, hForms⟩ := prop_as_forms d hd Jc Pc Xc Sf W Cp D hES
    Step Dbase Interp hcontract BD BDQ
  obtain ⟨δc, hδc, hCut⟩ := aux_cor_as_resolvent_hcut_supply hd Jc Pc Xc W Cp D Sf
    Step Dbase Interp
  obtain ⟨δu, hδu, hUnif⟩ := aux_cor_as_resolvent_hunif_supply hd Jc Pc Xc W Cp D Sf
    Step Dbase Interp
  refine ⟨min (min 1 δl) (min δf (min δc δu)),
    lt_min (lt_min one_pos hδl) (lt_min hδf (lt_min hδc hδu)), ?_⟩
  intro M Rm Sreg It H hH hM z r hr htri hz
  have h1 := hM.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hl := hM.trans (min_le_left _ _)
  have hf := hM.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc := hM.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hu := hM.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have HCUT := hCut M Rm Sreg It H hH hc
  have HUNIF := hUnif M Rm Sreg It H hH hu
  let hp := aux_mfd_prop_as_forms_poincare hd z r hr
  obtain ⟨G, hGm, hGae, _hrepresented⟩ :=
    hLimit M Rm Sreg It H hH hl HCUT HUNIF z r hr htri hp
  let GN : PUnit → BilateralField d → ℕ →
      (DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)) :=
    fun _ omega N => volumeResponseOperator (killedResponseSpace hp)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
  have hFG := hForms M Rm Sreg It H hH (le_min h1 hf) HCUT HUNIF z r hr PUnit
    (fun _ => z) (fun _ => r) (fun _ => hr) (fun _ => htri) (fun _ => hz)
    (fun _ => Set.Subset.rfl) (fun _ => hp) GN
    (fun _ _ _ _ => volumeResponseOperator_apply _ _ _)
  refine ⟨G, hGm, ?_⟩
  filter_upwards [hGae, hFG] with omega hL hF
  obtain ⟨G', hG', _huniq⟩ := hF PUnit.unit
  have hEq : G' = G omega := by
    apply ContinuousLinearMap.ext
    intro f
    have hpt : Tendsto (fun N => GN PUnit.unit omega N f) atTop (𝓝 (G' f)) :=
      ((continuous_id.clm_apply continuous_const).tendsto G').comp hG'.1.1
    have hActual : Tendsto (fun N => GN PUnit.unit omega N f) atTop (𝓝 (G omega f)) := by
      simpa only [GN, volumeResponseOperator_apply] using hL.1 f
    exact tendsto_nhds_unique hpt hActual
  rw [hEq] at hG'
  refine ⟨hG'.1.1, hG'.1.2.1, hG'.1.2.2.1, hG'.1.2.2.2.1,
    hG'.1.2.2.2.2, hG'.2.1, hG'.2.2.1, hG'.2.2.2, ?_⟩
  intro u hu
  obtain ⟨Ccoer, _hC, _hco, hdom⟩ := hL.2.2.2.1
  obtain ⟨v, hv, _hb⟩ := hdom u hu
  exact ⟨v, hv⟩

theorem aux_mfd_prop_as_forms_continuous_version
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (_hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (_hin : in_crossing M H PN KN)
    (hinput : aux_cutoff_lifetime_package_LocalInput M H KN)
    (hac : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (N : ℕ) (mu : ℝ), 0 < mu →
      ∀ (x : SpatialCoordinates d) (B : Set (SpatialCoordinates d)),
        MeasurableSet B → volume B = 0 →
          ∫ path, (∫ t in Set.Ioi (0 : ℝ),
              Real.exp (-mu * t) * B.indicator (fun _ => (1 : ℝ)) (path (Real.toNNReal t)))
            ∂(KN N (omega, x)) = 0)
    (qc : ℕ → SpatialCoordinates d) (qs : ℕ → ℝ)
    (hr : ∀ n : ℕ, 0 < qs n)
    (RN : ℕ → ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
        SpatialCoordinates d → ℝ)
    (hRN_formula : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
        (x : SpatialCoordinates d),
      RN n N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (qc n)
                (qs n) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x))) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (n N : ℕ) (lam : ℝ), 0 < lam →
      ∀ (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (U : SpatialCoordinates d → ℝ),
        ContinuousOn U (closure (centeredCube (qc n)
          (qs n) (hr n) : Set (SpatialCoordinates d))) →
        (RN n N omega lam f =ᵐ[volume.restrict (centeredCube (qc n)
          (qs n) (hr n) : Set (SpatialCoordinates d))] U) →
        ∀ x ∈ (centeredCube (qc n)
          (qs n) (hr n) : Set (SpatialCoordinates d)),
          RN n N omega lam f x = U x := by
  obtain ⟨L, hL, hLlocal, hLstrong⟩ :=
    aux_cutoff_lifetime_package_local M H KN hinput
  filter_upwards [hLstrong, hac] with omega hSMall hacω
  intro n N lam hlam f U hU hae x hx
  let Q : Set (SpatialCoordinates d) :=
    centeredCube (qc n)
      (qs n) (hr n)
  have hQ : IsOpen Q := by
    exact (centeredCube (qc n)
      (qs n) (hr n)).isOpen
  have hUQ : ContinuousOn U (closure Q) := by
    simpa [Q] using hU
  have hQsub : closure Q ⊆ Metric.closedBall
      (qc n)
      (qs n / 2) := by
    apply closure_minimal
    · simpa [Q, centeredCube] using
        (Metric.ball_subset_closedBall : Metric.ball
          (qc n)
          (qs n / 2) ⊆ _)
    · exact Metric.isClosed_closedBall
  have hQcompact : IsCompact (closure Q) := by
    exact (isCompact_closedBall (qc n)
      (qs n / 2)).of_isClosed_subset
        isClosed_closure hQsub
  let : CompactSpace (closure Q) := isCompact_iff_compactSpace.mp hQcompact
  let uC : C(closure Q, ℝ) :=
    ⟨fun z => U z, continuousOn_iff_continuous_domRestrict.mp hUQ⟩
  let uB : BoundedContinuousFunction (closure Q) ℝ :=
    BoundedContinuousFunction.mkOfCompact uC
  obtain ⟨g, hgrest⟩ :=
    uB.exists_norm_eq_domRestrict_eq_of_closed isClosed_closure
  have hgU : ∀ y ∈ closure Q, g y = U y := by
    intro y hy
    have hz := congrArg (fun v : BoundedContinuousFunction (closure Q) ℝ => v ⟨y, hy⟩)
      hgrest.2
    exact hz
  have hKprob : IsProbabilityMeasure (KN N (omega, x)) := by
    infer_instance
  let : IsMarkovKernel (L N omega) := ⟨fun y => ⟨(hSMall N).1 y⟩⟩
  have hRN_eq : ∀ y : SpatialCoordinates d,
      RN n N omega lam f y =
        (killedSMKS (L N omega) (hSMall N) Q hQ).kernelResolventReal lam
          (fun z => f z) y := by
    intro y
    rw [hRN_formula n N omega lam f y]
    exact aux_car_rn_continuous_version_path_resolvent
      (L N omega) (hSMall N) Q hQ (KN N (omega, y)) y
      (hL N omega y) hlam f.continuous.measurable
      (fun z => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm z)
  have hAEg :
      (fun y => (killedSMKS (L N omega) (hSMall N) Q hQ).kernelResolventReal lam
        (fun z => f z) y) =ᵐ[volume.restrict Q] g := by
    filter_upwards [hae, self_mem_ae_restrict hQ.measurableSet] with y hy hyQ
    rw [← hRN_eq y]
    exact hy.trans (hgU y (subset_closure hyQ)).symm
  let P := killedSMKS (L N omega) (hSMall N) Q hQ
  have hfD : ∀ y, |f y| ≤ ‖f‖ := by
    intro y
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm y
  have hgD : ∀ y, |g y| ≤ ‖g‖ := by
    intro y
    simpa [Real.norm_eq_abs] using g.norm_coe_le_norm y
  have hRlammeas : Measurable (P.kernelResolventReal lam (fun z => f z)) := by
    exact aux_car_rn_continuous_version_real_resolvent_measurable
      P hlam f.continuous.measurable hfD
  have hreplace : ∀ mu : ℝ, lam < mu →
      P.kernelResolventReal mu (fun y => P.kernelResolventReal lam (fun z => f z) y) x =
        P.kernelResolventReal mu (fun y => g y) x := by
    intro mu hlt
    have hmu : 0 < mu := hlam.trans hlt
    have hRlamD : ∀ y, |P.kernelResolventReal lam (fun z => f z) y| ≤
        ‖f‖ / lam := by
      intro y
      exact P.norm_kernelResolventReal_le hlam hfD y
    have hRlamG : Measurable (fun y => P.kernelResolventReal lam (fun z => f z) y) :=
      hRlammeas
    have hKNprob : IsProbabilityMeasure (KN N (omega, x)) := hKprob
    exact aux_car_rn_continuous_version_resolvent_congr_of_ae
      (L N omega) (hSMall N) Q hQ (KN N (omega, x)) x (hL N omega x)
      hmu hRlamG g.measurable hRlamD hgD hAEg
      (fun B hB hBzero => hacω N mu hmu x B hB hBzero)
  have heq : ∀ mu : ℝ, lam < mu →
      P.kernelResolventReal lam (fun z => f z) x =
        P.kernelResolventReal mu (fun z => f z) x + (mu - lam) *
          P.kernelResolventReal mu
            (fun y => P.kernelResolventReal lam (fun z => f z) y) x := by
    intro mu hlt
    simpa [P] using
      (aux_car_rn_continuous_version_real_resolvent_equation
        P hlam hlt f.continuous.measurable hfD x)
  have hfirst : Tendsto
      (fun mu : ℝ => P.kernelResolventReal mu (fun z => f z) x)
      atTop (nhds 0) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with mu hmu
      simpa [Real.norm_eq_abs] using P.norm_kernelResolventReal_le hmu hfD x
    · exact tendsto_const_nhds.div_atTop tendsto_id
  let F : ℝ → ℝ := fun t =>
    kernelIntegral (P (Real.toNNReal t)) (fun y => g y) x
  have hFmeas : Measurable F := by
    exact (P.measurable_kernelIntegral g.measurable).comp
      (measurable_real_toNNReal.prodMk measurable_const)
  have hFD : ∀ t, 0 < t → |F t| ≤ ‖g‖ := by
    intro t ht
    exact aux_car_rn_continuous_version_kernel_bound P hgD (Real.toNNReal t) x
  have hFzero : F 0 = g x := by
    change kernelIntegral (P (Real.toNNReal 0)) (fun y => g y) x = g x
    dsimp [P, killedSMKS]
    rw [Real.toNNReal_zero, killedFamily_zero]
    unfold kernelIntegral
    rw [Kernel.id_apply]
    simp
  have hF0 : ContinuousWithinAt F (Set.Ici (0 : ℝ)) 0 := by
    have hKzero : kernelIntegral
        (killedKernel (L N omega) Q hQ 0) g x = g x :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.goodCube_killedKernel_integral_zero_of_start
        (L N omega) (hSMall N) Q hQ g g.continuous.measurable hx
    have hcont := continuousWithinAt_killedKernel_integral
      (L N omega) Q hQ g x 0
    change Tendsto (fun r : ℝ => kernelIntegral
        (killedKernel (L N omega) Q hQ (Real.toNNReal r)) g x)
        (nhdsWithin (0 : ℝ) (Set.Ici 0))
        (nhds (kernelIntegral (killedKernel (L N omega) Q hQ (Real.toNNReal 0)) g x)) at hcont
    rw [Real.toNNReal_zero, hKzero] at hcont
    have hcont' : Tendsto
        (fun r : ℝ => kernelIntegral
          (killedKernel (L N omega) Q hQ (Real.toNNReal r)) g x)
        (nhdsWithin (0 : ℝ) (Set.Ici 0)) (nhds (g x)) := by
      exact hcont
    have heq : (fun r : ℝ => F r) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici 0)]
        (fun r : ℝ => kernelIntegral
          (killedKernel (L N omega) Q hQ (Real.toNNReal r)) g x) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr0 : 0 ≤ r := hr
      rcases eq_or_lt_of_le hr0 with rfl | hr
      · have hKzero' :
            kernelIntegral (killedKernel (L N omega) Q hQ (Real.toNNReal 0)) g x = g x := by
          simpa only [Real.toNNReal_zero] using hKzero
        exact hFzero.trans hKzero'.symm
      · have hrnn : Real.toNNReal r ≠ 0 := (Real.toNNReal_pos.mpr hr).ne'
        change kernelIntegral (P (Real.toNNReal r)) (fun y => g y) x = _
        dsimp [P, killedSMKS]
        rw [killedFamily_of_ne (L N omega) Q hQ hrnn]
    change Tendsto F (nhdsWithin (0 : ℝ) (Set.Ici 0)) (nhds (F 0))
    rw [hFzero]
    exact hcont'.congr' heq.symm
  have habel := aux_car_rn_continuous_version_abel hFmeas
    (norm_nonneg g) hFD hF0
  have hmuR : Tendsto
      (fun mu : ℝ => mu * P.kernelResolventReal mu (fun y => g y) x)
      atTop (nhds (g x)) := by
    simpa [F, hFzero, SubMarkovKernelSemigroup.kernelResolventReal] using habel
  have hfactor : Tendsto (fun mu : ℝ => (mu - lam) / mu)
      atTop (nhds (1 : ℝ)) := by
    have hdiv : Tendsto (fun mu : ℝ => lam / mu) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hsub : Tendsto (fun mu : ℝ => (1 : ℝ) - lam / mu)
        atTop (nhds ((1 : ℝ) - 0)) :=
      tendsto_const_nhds.sub hdiv
    have heq : (fun mu : ℝ => (mu - lam) / mu) =ᶠ[atTop]
        (fun mu : ℝ => 1 - lam / mu) := by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with mu hmu
      field_simp
    simpa only [sub_zero] using hsub.congr' heq.symm
  have hsecond : Tendsto
      (fun mu : ℝ => (mu - lam) * P.kernelResolventReal mu
        (fun y => g y) x) atTop (nhds (g x)) := by
    have hprod := hfactor.mul hmuR
    have heq : (fun mu : ℝ => (mu - lam) * P.kernelResolventReal mu
        (fun y => g y) x) =ᶠ[atTop]
        (fun mu : ℝ => ((mu - lam) / mu) *
          (mu * P.kernelResolventReal mu (fun y => g y) x)) := by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with mu hmu
      field_simp
    simpa only [one_mul] using hprod.congr' heq.symm
  have hRlim : P.kernelResolventReal lam (fun z => f z) x = g x := by
    have hsum : Tendsto
        (fun mu : ℝ => P.kernelResolventReal mu (fun z => f z) x +
          (mu - lam) * P.kernelResolventReal mu
            (fun y => P.kernelResolventReal lam (fun z => f z) y) x)
        atTop (nhds (g x)) := by
      have hcomp : Tendsto
          (fun mu : ℝ => (mu - lam) * P.kernelResolventReal mu
            (fun y => P.kernelResolventReal lam (fun z => f z) y) x)
          atTop (nhds (g x)) := by
        refine hsecond.congr' ?_
        filter_upwards [eventually_gt_atTop lam] with mu hmu
        rw [hreplace mu hmu]
      simpa only [zero_add] using hfirst.add hcomp
    have hconst : Tendsto
        (fun _ : ℝ => P.kernelResolventReal lam (fun z => f z) x)
        atTop (nhds (P.kernelResolventReal lam (fun z => f z) x)) :=
      tendsto_const_nhds
    have heq' : (fun mu : ℝ => P.kernelResolventReal mu (fun z => f z) x +
          (mu - lam) * P.kernelResolventReal mu
            (fun y => P.kernelResolventReal lam (fun z => f z) y) x) =ᶠ[atTop]
        (fun _ : ℝ => P.kernelResolventReal lam (fun z => f z) x) := by
      filter_upwards [eventually_gt_atTop lam] with mu hmu
      exact (heq mu hmu).symm
    have hconst' := hconst.congr' heq'.symm
    exact tendsto_nhds_unique hconst' hsum
  rw [hRN_eq x, hRlim, hgU x (subset_closure hx)]


theorem aux_mfd_prop_as_forms_osc_level_bound {d : ℕ} (hd : 2 ≤ d) (qc : SpatialCoordinates d) (qs : ℝ)
    (hr : 0 < qs)
    (K t : ℝ) (hK : 0 ≤ K) (ht : (d : ℝ) - 1 < t)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))))ᶜ = 0)
    (hgrowth : ∀ x ∈ closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → ν (Metric.ball x ρ) ≤ ENNReal.ofReal (K * ρ ^ t))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f 2 (volume.restrict (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d))))
    (V Ir : ℝ) (hV : ν.real univ ≤ V) (hIr : 0 ≤ Ir)
    (hI : aux_prop_uniform_resolvent_cutoff_oscillation_I (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d)) f ≤
        ENNReal.ofReal Ir)
    (m : ℕ) :
    eLpNorm (fun x => aux_prop_uniform_resolvent_cutoff_oscillation_E (qc)
        (qs) hr f (m + 1) x -
      aux_prop_uniform_resolvent_cutoff_oscillation_E (qc)
        (qs) hr f m x) 2 ν ≤
      ENNReal.ofReal (Real.sqrt ((K + V) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - t)) * (qs) ^ (t - d + 1) * Ir) *
        (Real.sqrt ((3 : ℝ) ^ (-(t - d + 1)))) ^ m) := by
  set s := qs with hsdef
  have hinc := SubdiffusiveProcess.Section9.cubeTriadicAverages_memLp_and_increment_bound hd
    qc hr K t hK ht m ν inferInstance hsupp hgrowth f hf
  dsimp only at hinc
  have hsq := hinc.2.2
  have hα : 0 < t - d + 1 := by linarith
  set C0 : ℝ := (Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * (3 : ℝ) ^ ((d : ℝ) - t) with hC0
  have hC0nn : 0 ≤ C0 := by positivity
  have hcoef := aux_prop_uniform_resolvent_cutoff_oscillation_level_coeff (d := d) s t hr m
  have hscale := aux_prop_uniform_resolvent_cutoff_oscillation_level_scale_pow s (t - d + 1) hr m
  set ell : ℝ := s / (2 * (triadicHalf m : ℝ) + 1) with hell
  have hellpos : 0 < ell := by rw [hell]; positivity
  have hVnn : 0 ≤ ν.real univ := measureReal_nonneg
  have hq0 : 0 ≤ (3 : ℝ) ^ (-(t - d + 1)) := by positivity
  set q : ℝ := Real.sqrt ((3 : ℝ) ^ (-(t - d + 1))) with hqdef
  have hq2 : q ^ 2 = (3 : ℝ) ^ (-(t - d + 1)) := Real.sq_sqrt hq0
  set X : ℝ := (K + V) * C0 * s ^ (t - d + 1) * Ir with hX
  have hXnn : 0 ≤ X := by
    have : 0 ≤ K + V := by linarith
    positivity
  apply aux_prop_uniform_resolvent_cutoff_oscillation_ennreal_le_of_sq_le (by positivity)
  refine hsq.trans ?_
  have hsqrtd : 0 ≤ Real.sqrt (d : ℝ) * ell := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hsqrtd (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal ((K + ν.real univ) * (ell / 3) ^ t * ((ell / 3) ^ d * ell ^ d)⁻¹ *
          (Real.sqrt (d : ℝ) * ell) ^ ((d : ℝ) + 1)) *
        aux_prop_uniform_resolvent_cutoff_oscillation_I (centeredCube (qc) s hr :
          Set (SpatialCoordinates d)) f
      ≤ ENNReal.ofReal ((K + ν.real univ) * (ell / 3) ^ t * ((ell / 3) ^ d * ell ^ d)⁻¹ *
          (Real.sqrt (d : ℝ) * ell) ^ ((d : ℝ) + 1)) * ENNReal.ofReal Ir := by
        gcongr
    _ = ENNReal.ofReal ((K + ν.real univ) * (C0 * (s ^ (t - d + 1) * ((3 : ℝ) ^ (-(t - d + 1))) ^ m))
          * Ir) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [mul_assoc (K + ν.real univ), mul_assoc (K + ν.real univ), hell, hcoef, hscale]
    _ ≤ ENNReal.ofReal ((Real.sqrt X * q ^ m) ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_pow, Real.sq_sqrt hXnn, ← pow_mul, mul_comm m 2, pow_mul, hq2, hX]
        have hA : 0 ≤ C0 * (s ^ (t - d + 1) * ((3 : ℝ) ^ (-(t - d + 1))) ^ m) := by positivity
        have hB : K + ν.real univ ≤ K + V := by linarith
        calc (K + ν.real univ) * (C0 * (s ^ (t - d + 1) * ((3 : ℝ) ^ (-(t - d + 1))) ^ m)) * Ir
            ≤ (K + V) * (C0 * (s ^ (t - d + 1) * ((3 : ℝ) ^ (-(t - d + 1))) ^ m)) * Ir := by
              gcongr
          _ = (K + V) * C0 * s ^ (t - d + 1) * Ir * ((3 : ℝ) ^ (-(t - d + 1))) ^ m := by ring

theorem aux_mfd_prop_as_forms_osc_trace_diff {d : ℕ} (hd : 2 ≤ d) (qc : SpatialCoordinates d) (qs : ℝ)
    (hr : 0 < qs)
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (μ : Measure (SpatialCoordinates d))
    (hac : μ.restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) ≪ volume)
    (Km V0 : ℝ) (hKm : 0 ≤ Km) (hV0 : 0 ≤ V0)
    (hgrowth : ∀ x ∈ closure (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d)), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → μ (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ t))
    (hV : μ (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d)) ≤
      ENNReal.ofReal V0)
    (φ : SpatialCoordinates d → ℝ)
    (hφ : MemLp φ 2 (volume.restrict (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d))))
    (Ir : ℝ) (hIr : 0 ≤ Ir)
    (hI : aux_prop_uniform_resolvent_cutoff_oscillation_I (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d)) φ ≤
        ENNReal.ofReal Ir)
    (n : ℕ) :
    eLpNorm (fun x => φ x - aux_prop_uniform_resolvent_cutoff_oscillation_E (qc)
        (qs) hr φ n x) 2
      (μ.restrict (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d))) ≤
      ENNReal.ofReal (Real.sqrt ((Km + V0) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - t)) * (qs) ^ (t - d + 1) * Ir) *
        (Real.sqrt ((3 : ℝ) ^ (-(t - d + 1)))) ^ n /
          (1 - Real.sqrt ((3 : ℝ) ^ (-(t - d + 1))))) := by
  set z := qc with hzdef
  set s := qs with hsdef
  set Q : Set (SpatialCoordinates d) := (centeredCube z s hr : Set (SpatialCoordinates d))
    with hQdef
  set ν := μ.restrict Q with hνdef
  have : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hνdef, Measure.restrict_apply_univ]
    exact hV.trans_lt ENNReal.ofReal_lt_top
  have hQeq : Q = (centeredCube qc qs hr : Set (SpatialCoordinates d)) := (rfl : (centeredCube qc qs hr : Set (SpatialCoordinates d)) = _)
  have hsupp : ν (closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))))ᶜ = 0 := by
    rw [← hQeq, hνdef, Measure.restrict_apply isClosed_closure.isOpen_compl.measurableSet]
    have : (closure Q)ᶜ ∩ Q = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      exact hx.1 (subset_closure hx.2)
    rw [this, measure_empty]
  have hgrowthν : ∀ x ∈ closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → ν (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ t) := by
    intro x hx ρ hρ hρ1
    rw [← hQeq] at hx
    exact (Measure.restrict_apply_le Q _).trans (hgrowth x hx ρ hρ hρ1)
  have hVr : ν.real univ ≤ V0 := by
    rw [measureReal_def, hνdef, Measure.restrict_apply_univ]
    exact ENNReal.toReal_le_of_le_ofReal hV0 hV
  have hα : 0 < t - d + 1 := by linarith
  have hq0' : 0 ≤ (3 : ℝ) ^ (-(t - d + 1)) := by positivity
  have hq1' : (3 : ℝ) ^ (-(t - d + 1)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set q : ℝ := Real.sqrt ((3 : ℝ) ^ (-(t - d + 1))) with hqdef
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q < 1 := by
    rw [hqdef, Real.sqrt_lt' one_pos, one_pow]
    exact hq1'
  have hstep : ∀ m, n ≤ m →
      eLpNorm (fun x => aux_prop_uniform_resolvent_cutoff_oscillation_E z s hr φ (m + 1) x - aux_prop_uniform_resolvent_cutoff_oscillation_E z s hr φ m x) 2 ν ≤
        ENNReal.ofReal (Real.sqrt ((Km + V0) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - t)) * s ^ (t - d + 1) * Ir) * q ^ m) :=
    fun m _ => aux_mfd_prop_as_forms_osc_level_bound hd qc qs hr Km t hKm ht ν hsupp hgrowthν φ hφ V0 Ir hVr hIr
      hI m
  have hint : IntegrableOn φ Q volume := hφ.integrable one_le_two
  have hleb := aux_prop_uniform_resolvent_cutoff_oscillation_triadic_tendsto_ae hd z hr φ hint
  have hνac : ν ≪ volume := hac
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun m => aux_prop_uniform_resolvent_cutoff_oscillation_E z s hr φ m x) atTop (𝓝 (φ x)) := by
    filter_upwards [hνac.ae_le hleb, ae_restrict_mem (centeredCube z s hr).isOpen.measurableSet]
      with x hx hxQ
    exact hx hxQ
  exact aux_prop_uniform_resolvent_cutoff_oscillation_fatou_tail ν (fun m => aux_prop_uniform_resolvent_cutoff_oscillation_E z s hr φ m) φ
    (fun m => (aux_prop_uniform_resolvent_cutoff_oscillation_E_measurable z hr φ m).aestronglyMeasurable) hlim n _ q
    (Real.sqrt_nonneg _) hq0 hq1 hstep

theorem aux_mfd_prop_as_forms_osc_w_bound {d : ℕ} (hd : 2 ≤ d) (qc : SpatialCoordinates d) (qs : ℝ)
    (hr : 0 < qs)
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (μ : Measure (SpatialCoordinates d))
    (hac : μ.restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) ≪ volume)
    (Km V0 Kc B : ℝ) (hKm : 0 ≤ Km) (hV0 : 0 ≤ V0) (hKc : 0 ≤ Kc) (hB : 0 ≤ B)
    (hgrowth : ∀ x ∈ closure (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d)), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → μ (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ t))
    (hV : μ (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d)) ≤
      ENNReal.ofReal V0)
    (a : PositiveCoefficient (centeredCube (qc)
      (qs) hr))
    (w : killedSobolevGraph (centeredCube (qc)
      (qs) hr))
    (hcw1 : ‖(w : SobolevData (centeredCube (qc)
        (qs) hr)).1‖ ^ 2 ≤
      Kc * sobolevCoefficientForm a w.val w.val)
    (hcw2 : globalFractionalSqNorm (3 / 4)
        (Set.indicator ((centeredCube (qc)
          (qs) hr) : Set (SpatialCoordinates d))
          (fun x => (w : SobolevData (centeredCube (qc)
            (qs) hr)).1 x)) ≤
      ENNReal.ofReal (Kc * sobolevCoefficientForm a w.val w.val))
    (h : SpatialCoordinates d → ℝ)
    (hh : AEStronglyMeasurable h (μ.restrict (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d))))
    (hbound : ∀ᵐ x ∂(μ.restrict (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d))), |h x| ≤ B)
    (n : ℕ)
    (hEw : sobolevCoefficientForm a w.val w.val =
      (∫ x in (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d)),
        h x * (w : SobolevData (centeredCube (qc)
          (qs) hr)).1 x ∂μ) -
      ∫ x, h x * aux_prop_uniform_resolvent_cutoff_oscillation_E (qc)
          (qs) hr
          (fun y => (w : SobolevData (centeredCube (qc)
            (qs) hr)).1 y) n x
        ∂(μ.restrict (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d)))) :
    ‖(w : SobolevData (centeredCube (qc)
        (qs) hr)).1‖ ^ 2 ≤
      Kc ^ 2 * V0 * ((Km + V0) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - t)) *
          (Real.sqrt (d : ℝ) * qs) ^ (1 / 2 : ℝ)) /
        (1 - Real.sqrt ((3 : ℝ) ^ (-(t - d + 1)))) ^ 2 * B ^ 2 *
        (qs / (3 : ℝ) ^ n) ^ (t - d + 1) := by
  have : IsFiniteMeasure (μ.restrict (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hV.trans_lt ENNReal.ofReal_lt_top
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = sobolevCoefficientForm a w.val w.val := ⟨_, rfl⟩
  rw [← hEdef] at hcw1 hcw2 hEw
  have hE0 : 0 ≤ E := by rw [hEdef]; exact sobolevCoefficientForm_nonneg a _
  have hφ2 : MemLp (fun y => (w : SobolevData (centeredCube (qc)
      (qs) hr)).1 y) 2
      (volume.restrict (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d))) := Lp.memLp _
  have hφs : StronglyMeasurable (fun y => (w : SobolevData (centeredCube
      (qc) (qs) hr)).1 y) :=
    Lp.stronglyMeasurable _
  obtain ⟨cs, hcsdef⟩ : ∃ cs : ℝ,
      cs = (Real.sqrt (d : ℝ) * qs) ^ (1 / 2 : ℝ) :=
    ⟨_, rfl⟩
  have hcs0 : 0 ≤ cs := by rw [hcsdef]; positivity
  obtain ⟨C0, hC0def⟩ : ∃ C0 : ℝ,
      C0 = (Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * (3 : ℝ) ^ ((d : ℝ) - t) := ⟨_, rfl⟩
  have hC00 : 0 ≤ C0 := by rw [hC0def]; positivity
  have hIr0 : 0 ≤ cs * (Kc * E) := by positivity
  have hI : aux_prop_uniform_resolvent_cutoff_oscillation_I (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d))
      (fun y => (w : SobolevData (centeredCube (qc)
        (qs) hr)).1 y) ≤ ENNReal.ofReal (cs * (Kc * E)) := by
    refine (aux_prop_uniform_resolvent_cutoff_oscillation_kernel_compare _ hr _ hφs.measurable).trans ?_
    rw [ENNReal.ofReal_mul hcs0, ← hcsdef]
    gcongr
  have hT := aux_mfd_prop_as_forms_osc_trace_diff hd qc qs hr t ht μ hac Km V0 hKm hV0 hgrowth hV _ hφ2
    (cs * (Kc * E)) hIr0 hI n
  rw [← hC0def] at hT
  have hα : 0 < t - d + 1 := by linarith
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = Real.sqrt ((3 : ℝ) ^ (-(t - d + 1))) := ⟨_, rfl⟩
  rw [← hqdef] at hT ⊢
  have hq0' : 0 ≤ (3 : ℝ) ^ (-(t - d + 1)) := by positivity
  have hq1 : q < 1 := by
    rw [hqdef, Real.sqrt_lt' one_pos, one_pow]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq0 : 0 ≤ q := by rw [hqdef]; exact Real.sqrt_nonneg _
  have h1q : 0 < 1 - q := by linarith
  have hT0 : 0 ≤ Real.sqrt ((Km + V0) * C0 * qs ^ (t - d + 1) * (cs * (Kc * E))) * q ^ n /
      (1 - q) := by positivity
  have hpair := aux_prop_uniform_resolvent_cutoff_oscillation_pair_diff_bound _ h _ _ B _ hB hT0 hh hbound hφs.aestronglyMeasurable
    (aux_prop_uniform_resolvent_cutoff_oscillation_E_memLp _ hr _ n _) hT
  have hVr : Real.sqrt ((μ.restrict (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d))).real univ) ≤
      Real.sqrt V0 := by
    apply Real.sqrt_le_sqrt
    rw [measureReal_def, Measure.restrict_apply_univ]
    exact ENNReal.toReal_le_of_le_ofReal hV0 hV
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = B * Real.sqrt V0 *
      (Real.sqrt ((Km + V0) * C0 * qs ^ (t - d + 1) * (cs * Kc)) * q ^ n / (1 - q)) := ⟨_, rfl⟩
  have hEA : E ≤ A * Real.sqrt E := by
    have h1 := hpair.2.2
    rw [← hEw] at h1
    have h3 : Real.sqrt ((Km + V0) * C0 * qs ^ (t - d + 1) * (cs * (Kc * E))) * q ^ n /
        (1 - q) = Real.sqrt ((Km + V0) * C0 * qs ^ (t - d + 1) * (cs * Kc)) * q ^ n / (1 - q) *
        Real.sqrt E := by
      rw [show (Km + V0) * C0 * qs ^ (t - d + 1) * (cs * (Kc * E)) =
        ((Km + V0) * C0 * qs ^ (t - d + 1) * (cs * Kc)) * E by ring,
        Real.sqrt_mul' _ hE0]
      ring
    rw [h3] at h1
    calc E ≤ B * Real.sqrt ((μ.restrict (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))).real univ) *
          (Real.sqrt ((Km + V0) * C0 * qs ^ (t - d + 1) * (cs * Kc)) * q ^ n / (1 - q) *
            Real.sqrt E) := h1
      _ ≤ B * Real.sqrt V0 *
          (Real.sqrt ((Km + V0) * C0 * qs ^ (t - d + 1) * (cs * Kc)) * q ^ n / (1 - q) *
            Real.sqrt E) := by gcongr
      _ = A * Real.sqrt E := by rw [hAdef]; ring
  have hEA2 := aux_prop_uniform_resolvent_cutoff_oscillation_sqrt_absorb E A hE0 hEA
  have hKmV : 0 ≤ Km + V0 := by linarith
  have hscale := aux_prop_uniform_resolvent_cutoff_oscillation_level_scale_pow _ (t - d + 1) hr n
  have hq2 : q ^ 2 = (3 : ℝ) ^ (-(t - d + 1)) := by rw [hqdef]; exact Real.sq_sqrt hq0'
  rw [← hC0def, ← hcsdef]
  calc _ ≤ Kc * E := hcw1
    _ ≤ Kc * A ^ 2 := mul_le_mul_of_nonneg_left hEA2 hKc
    _ = Kc ^ 2 * V0 * ((Km + V0) * C0 * cs) / (1 - q) ^ 2 * B ^ 2 *
          (qs / (3 : ℝ) ^ n) ^ (t - d + 1) := by
        have hsq1 : Real.sqrt V0 ^ 2 = V0 := Real.sq_sqrt hV0
        have hsq2 : Real.sqrt ((Km + V0) * C0 * qs ^ (t - d + 1) *
            (cs * Kc)) ^ 2 = (Km + V0) * C0 * qs ^ (t - d + 1) *
            (cs * Kc) := Real.sq_sqrt (by positivity)
        have hq2n : (q ^ n) ^ 2 = ((3 : ℝ) ^ (-(t - d + 1))) ^ n := by
          rw [← pow_mul, mul_comm n 2, pow_mul, hq2]
        rw [hscale, hAdef, mul_pow, mul_pow, div_pow, mul_pow, hsq1, hsq2, hq2n]
        field_simp

theorem aux_mfd_prop_as_forms_osc_instance {d : ℕ} (hd : 2 ≤ d) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon < 1)
    (qc : SpatialCoordinates d) (qs : ℝ) (hr : 0 < qs)
    (μ : Measure (SpatialCoordinates d))
    (hac : μ.restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) ≪ volume)
    (Km V0 Kc Kh : ℝ) (hKm : 0 ≤ Km) (hV0 : 0 ≤ V0) (hKc : 0 ≤ Kc) (hKh : 0 ≤ Kh)
    (hgrowth : ∀ x ∈ closure (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      μ (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ ((d : ℝ) - epsilon)))
    (hV : μ (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) ≤ ENNReal.ofReal V0)
    (a : PositiveCoefficient (centeredCube (qc) (qs) hr))
    (hcoer : ∀ v : killedSobolevGraph (centeredCube (qc) (qs) hr),
      ‖(v : SobolevData (centeredCube (qc) (qs) hr)).1‖ ^ 2 ≤ Kc * sobolevCoefficientForm a v.val v.val ∧
      globalFractionalSqNorm (3 / 4)
        (Set.indicator (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) (fun x => (v : SobolevData (centeredCube (qc) (qs) hr)).1 x)) ≤
        ENNReal.ofReal (Kc * sobolevCoefficientForm a v.val v.val))
    (hHol : ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 → ∀ MF : ℝ, 0 ≤ MF →
      (∀ x ∈ (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), |F0 x| ≤ MF) → ∀ v : killedSobolevGraph (centeredCube (qc) (qs) hr),
        (∀ w : killedSobolevGraph (centeredCube (qc) (qs) hr), sobolevCoefficientForm a v.val w.val =
          ∫ x in (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), F0 x * (w : SobolevData (centeredCube (qc) (qs) hr)).1 x) →
        ∃ vc : C(SpatialCoordinates d, ℝ),
          (((v : SobolevData (centeredCube (qc) (qs) hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d))] vc) ∧
          (∀ x ∉ (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), vc x = 0) ∧
          (∀ x ∈ closure (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), ∀ y ∈ closure (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)),
            |vc x - vc y| ≤ Kh * MF * dist x y ^ (1 / 2 : ℝ)))
    (u : killedSobolevGraph (centeredCube (qc) (qs) hr)) (h : SpatialCoordinates d → ℝ)
    (hh : AEStronglyMeasurable h (μ.restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)))) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂(μ.restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d))), |h x| ≤ B)
    (hfin : ∀ w : killedSobolevGraph (centeredCube (qc) (qs) hr), sobolevCoefficientForm a u.val w.val =
      ∫ x in (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), h x * (w : SobolevData (centeredCube (qc) (qs) hr)).1 x ∂μ)
    (u0 : SpatialCoordinates d → ℝ)
    (hzero : ∀ x, u0 x = Set.indicator (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) (fun y => (u : SobolevData (centeredCube (qc) (qs) hr)).1 y) x)
    (x : SpatialCoordinates d) (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∫ y in Metric.ball x r,
        (u0 y - (volume.real (Metric.ball x r))⁻¹ * ∫ w in Metric.ball x r, u0 w) ^ 2) ≤
      (aux_prop_uniform_resolvent_cutoff_oscillation_Kinst d epsilon (qs) Km V0 Kc Kh * B) ^ 2 *
        volume.real (Metric.ball x r) * r ^ (2 * (1 / 2 - ((d : ℝ) + 2) * epsilon)) := by
  have hQm : MeasurableSet (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) := (centeredCube (qc) (qs) hr).isOpen.measurableSet
  have : IsFiniteMeasure (μ.restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hV.trans_lt ENNReal.ofReal_lt_top
  have hR0 : 0 < r ^ ((d : ℝ) + 2) := Real.rpow_pos_of_pos hr0 _
  have hR1 : r ^ ((d : ℝ) + 2) ≤ 1 := Real.rpow_le_one hr0.le hr1 (by positivity)
  obtain ⟨n, hn1, hn2⟩ := aux_prop_uniform_resolvent_cutoff_oscillation_level_choice (qs)
    (r ^ ((d : ℝ) + 2)) hr hR0 hR1
  have ht0 : 0 < (d : ℝ) - epsilon := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have htd : (d : ℝ) - 1 < (d : ℝ) - epsilon := by linarith
  have hℓpos : 0 < qs / (3 : ℝ) ^ n := by positivity
  have hℓ2 : qs / (3 : ℝ) ^ n ≤ 2 := by linarith
  obtain ⟨MF, hMFdef⟩ : ∃ MF : ℝ, MF = B * Km *
      (qs / (3 : ℝ) ^ n) ^ ((d : ℝ) - epsilon) /
        (qs / (3 : ℝ) ^ n) ^ d := ⟨_, rfl⟩
  have hMF0 : 0 ≤ MF := by rw [hMFdef]; positivity
  have hF0b : ∀ y, |aux_prop_uniform_resolvent_cutoff_oscillation_source (qc)
      (qs) hr (μ.restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d))) h n y| ≤ MF := by
    intro y
    rw [hMFdef]
    exact aux_prop_uniform_resolvent_cutoff_oscillation_source_bound _ hr μ h B hB hbound Km _ hKm ht0 hgrowth n hℓ2 y
  have hF0m := aux_prop_uniform_resolvent_cutoff_oscillation_source_measurable (qc) hr
    (μ.restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d))) h n
  have hF0L2 : MemLp (aux_prop_uniform_resolvent_cutoff_oscillation_source (qc)
      (qs) hr (μ.restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d))) h n) 2 (volume.restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d))) :=
    MemLp.of_bound hF0m.aestronglyMeasurable MF
      (ae_of_all _ (fun y => by rw [Real.norm_eq_abs]; exact hF0b y))
  obtain ⟨v, hv⟩ := aux_prop_uniform_resolvent_cutoff_oscillation_comparison_exists a Kc (fun v => (hcoer v).1) _ hF0L2
  obtain ⟨vc, hvcae, hvc0, hvcHol⟩ := hHol _ hF0m MF hMF0 (fun y _ => hF0b y) v hv
  have hC : 0 ≤ Kh * MF := mul_nonneg hKh hMF0
  have hglob := aux_prop_uniform_resolvent_cutoff_oscillation_holder_global (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) (centeredCube (qc) (qs) hr).isOpen vc (Kh * MF) hC hvc0 hvcHol
  have hhint : Integrable h (μ.restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d))) := by
    refine Integrable.mono' (integrable_const B) hh ?_
    filter_upwards [hbound] with y hy
    simpa [Real.norm_eq_abs] using hy
  have hwint : IntegrableOn (fun y => ((u - v : killedSobolevGraph (centeredCube (qc) (qs) hr)) :
      SobolevData (centeredCube (qc) (qs) hr)).1 y) (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) volume :=
    (Lp.memLp _).integrable one_le_two
  have hpair := aux_prop_uniform_resolvent_cutoff_oscillation_pairing (qc) hr n (μ.restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d))) h hhint
    _ hwint
  have hEw : sobolevCoefficientForm a (u - v : killedSobolevGraph (centeredCube (qc) (qs) hr)).val
      (u - v : killedSobolevGraph (centeredCube (qc) (qs) hr)).val =
      (∫ y in (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), h y * ((u - v : killedSobolevGraph (centeredCube (qc) (qs) hr)) : SobolevData (centeredCube (qc) (qs) hr)).1 y ∂μ) -
      ∫ y, h y * aux_prop_uniform_resolvent_cutoff_oscillation_E (qc)
          (qs) hr
          (fun z => ((u - v : killedSobolevGraph (centeredCube (qc) (qs) hr)) : SobolevData (centeredCube (qc) (qs) hr)).1 z) n y
        ∂(μ.restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d))) := by
    rw [aux_prop_uniform_resolvent_cutoff_oscillation_form_sub, hfin, hv, hpair]
  have hwb := aux_mfd_prop_as_forms_osc_w_bound hd qc qs hr ((d : ℝ) - epsilon) htd μ hac Km V0 Kc B hKm hV0 hKc
    hB hgrowth hV a (u - v) (hcoer (u - v)).1 (hcoer (u - v)).2 h hh hbound n hEw
  have hdecomp := aux_prop_uniform_resolvent_cutoff_oscillation_decomp (centeredCube (qc) (qs) hr) u v vc hvcae hvc0 u0 hzero
  have hW2 := (aux_prop_uniform_resolvent_cutoff_oscillation_L2_norm_sq
    ((u - v : killedSobolevGraph (centeredCube (qc)
      (qs) hr)) : SobolevData (centeredCube
        (qc) (qs) hr)).1).trans_le hwb
  have hcamp := aux_prop_uniform_resolvent_cutoff_oscillation_campanato_assembly (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) hQm u0 vc _ vc.continuous (Kh * MF) hC hglob
    hdecomp (Lp.memLp _) _ hW2 x r
  refine hcamp.trans ?_
  have hvol : volume.real (Metric.ball x r) = (2 * r) ^ d := by
    rw [measureReal_def, Real.volume_pi_ball x hr0, Fintype.card_fin,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hvol, hMFdef]
  have hσ : 0 < min (qs) (1 / 3) := lt_min hr (by norm_num)
  have hCw : 0 ≤ Kc ^ 2 * V0 * ((Km + V0) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
        (3 : ℝ) ^ ((d : ℝ) - ((d : ℝ) - epsilon))) *
        (Real.sqrt (d : ℝ) * qs) ^ (1 / 2 : ℝ)) /
      (1 - Real.sqrt ((3 : ℝ) ^ (-((d : ℝ) - epsilon - d + 1)))) ^ 2 := by
    have : 0 ≤ Km + V0 := by linarith
    positivity
  exact aux_prop_uniform_resolvent_cutoff_oscillation_final_algebra (d := d) epsilon r _ _ B Km Kh _ hepsilon hepsilon1 hr0 hr1 hσ hCw
    hn1 hn2

theorem aux_mfd_prop_as_forms_osc_cover {d : ℕ} (qc : SpatialCoordinates d) (qs : ℝ)
    (hr : 0 < qs) :
    ∃ V1 : ℝ, 0 ≤ V1 ∧ ∀ (μ : Measure (SpatialCoordinates d)) (Km : ℝ), 0 ≤ Km →
      (∀ x ∈ closure (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), μ (Metric.ball x 1) ≤ ENNReal.ofReal Km) →
      μ (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) ≤ ENNReal.ofReal (V1 * Km) := by
  have hcomp : IsCompact (closure (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d))) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (centeredCube_isBounded _ hr).closure
  obtain ⟨T, hTsub, hTfin, hcover⟩ := finite_cover_balls_of_compact hcomp one_pos
  refine ⟨(hTfin.toFinset.card : ℝ), Nat.cast_nonneg _, ?_⟩
  intro μ Km hKm hball
  have hsub : (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) ⊆ ⋃ x ∈ hTfin.toFinset, Metric.ball x 1 := by
    intro y hy
    have := hcover (subset_closure hy)
    simp only [Set.mem_iUnion] at this ⊢
    obtain ⟨x, hxT, hyx⟩ := this
    exact ⟨x, hTfin.mem_toFinset.2 hxT, hyx⟩
  calc μ (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) ≤ μ (⋃ x ∈ hTfin.toFinset, Metric.ball x 1) := measure_mono hsub
    _ ≤ ∑ x ∈ hTfin.toFinset, μ (Metric.ball x 1) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ hTfin.toFinset, ENNReal.ofReal Km := by
        exact Finset.sum_le_sum (fun x hx => hball x (hTsub (hTfin.mem_toFinset.1 hx)))
    _ = ENNReal.ofReal ((hTfin.toFinset.card : ℝ) * Km) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

theorem aux_mfd_prop_as_forms_osc_omega {d : ℕ} (hd : 2 ≤ d)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (qc : SpatialCoordinates d) (qs : ℝ)
    (hr : 0 < qs)
    (muN : ℕ → Measure (SpatialCoordinates d))
    (E : ℕ → killedSobolevGraph (centeredCube (qc) (qs) hr) → killedSobolevGraph (centeredCube (qc) (qs) hr) → ℝ)
    (RN : ℕ → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      SpatialCoordinates d → ℝ)
    (uN : ℕ → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      killedSobolevGraph (centeredCube (qc) (qs) hr))
    (uN0 : ℕ → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      SpatialCoordinates d → ℝ)
    (aN : ℕ → PositiveCoefficient (centeredCube (qc) (qs) hr))
    (hE : ∀ N v w, E N v w = sobolevCoefficientForm (aN N) v.val w.val)
    (hRNmeas : ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        AEMeasurable (RN N lam f) ((muN N).restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d))))
    (hsource : ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ᵐ x ∂((muN N).restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d))), |f x - lam * RN N lam f x| ≤ 2 * ‖f‖)
    (Kmu : ℝ) (Kcoer Khol : ℕ → ℝ)
    (hconstants : BddAbove (Set.range (fun N => Kcoer N)) ∧
      BddAbove (Set.range (fun N => Khol N)))
    (Region : Set (SpatialCoordinates d))
    (hNeighborhood : ∀ x ∈ closure (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), Metric.ball x 1 ⊆ Region)
    (hfinite : ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ w : killedSobolevGraph (centeredCube (qc) (qs) hr),
          E N (uN N lam f) w =
            ∫ x in (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), (f x - lam * RN N lam f x) * (w : SobolevData (centeredCube (qc) (qs) hr)).1 x ∂(muN N))
    (hzero : ∀ N : ℕ, ∀ lam : ℝ, ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ x : SpatialCoordinates d,
        uN0 N lam f x = Set.indicator (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) (fun y => ((uN N lam f : SobolevData (centeredCube (qc) (qs) hr)).1 y)) x)
    (hgrowth : ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ N, muN N (Metric.ball x r) ≤ ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon)))
    (hcoer : ∀ N : ℕ, ∀ v : killedSobolevGraph (centeredCube (qc) (qs) hr),
      ‖(v : SobolevData (centeredCube (qc) (qs) hr)).1‖ ^ 2 ≤ Kcoer N * E N v v ∧
      globalFractionalSqNorm (3 / 4) (Set.indicator (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) (fun x => (v : SobolevData (centeredCube (qc) (qs) hr)).1 x)) ≤
        ENNReal.ofReal (Kcoer N * E N v v))
    (hHolder : ∀ N : ℕ, ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 →
      ∀ MF : ℝ, 0 ≤ MF → (∀ x ∈ (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), |F0 x| ≤ MF) →
      ∀ v : killedSobolevGraph (centeredCube (qc) (qs) hr),
        (∀ w : killedSobolevGraph (centeredCube (qc) (qs) hr),
          E N v w = ∫ x in (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), F0 x * (w : SobolevData (centeredCube (qc) (qs) hr)).1 x) →
        ∃ vc : C(SpatialCoordinates d, ℝ),
          (((v : SobolevData (centeredCube (qc) (qs) hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d))] vc) ∧
          (∀ x ∉ (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), vc x = 0) ∧
          (∀ x ∈ closure (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), ∀ y ∈ closure (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)),
            |vc x - vc y| ≤ Khol N * MF * dist x y ^ (1 / 2 : ℝ)))
    (hac : ∀ N, (muN N).restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) ≪ volume) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ N : ℕ, ∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ x : SpatialCoordinates d, ∀ r : ℝ, 0 < r → r ≤ 1 →
            (∫ y in Metric.ball x r,
              (uN0 N lam f y -
                (volume.real (Metric.ball x r))⁻¹ *
                  ∫ w in Metric.ball x r, uN0 N lam f w) ^ 2) ≤
              (K * ‖f‖) ^ 2 * volume.real (Metric.ball x r) *
                r ^ (2 * (1 / 2 - ((d : ℝ) + 2) * epsilon)) := by
  obtain ⟨Cc, hCc⟩ := hconstants.1
  obtain ⟨Ch, hCh⟩ := hconstants.2
  have hKc : ∀ N, Kcoer N ≤ max Cc 0 := fun N => (hCc ⟨N, rfl⟩).trans (le_max_left _ _)
  have hKh : ∀ N, Khol N ≤ max Ch 0 := fun N => (hCh ⟨N, rfl⟩).trans (le_max_left _ _)
  have hKc0 : 0 ≤ max Cc 0 := le_max_right _ _
  have hKh0 : 0 ≤ max Ch 0 := le_max_right _ _
  have hKm0 : 0 ≤ max Kmu 0 := le_max_right _ _
  have hε1 : epsilon < 1 := by
    have h8 : (1 : ℝ) ≤ 8 * ((d : ℝ) + 2) := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have : 1 / (8 * ((d : ℝ) + 2)) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact h8
    linarith
  have hgrowthN : ∀ N, ∀ x ∈ closure (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      muN N (Metric.ball x ρ) ≤ ENNReal.ofReal (max Kmu 0 * ρ ^ ((d : ℝ) - epsilon)) := by
    intro N x hx ρ hρ hρ1
    refine (hgrowth x (hNeighborhood x hx (Metric.mem_ball_self one_pos)) ρ hρ hρ1 N).trans ?_
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hρ.le _)
  obtain ⟨V1, hV1, hcov⟩ := aux_mfd_prop_as_forms_osc_cover qc qs hr
  have hV : ∀ N, muN N (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) ≤ ENNReal.ofReal (V1 * max Kmu 0) := by
    intro N
    apply hcov (muN N) (max Kmu 0) hKm0
    intro x hx
    have := hgrowthN N x hx 1 one_pos le_rfl
    rwa [Real.one_rpow, mul_one] at this
  refine ⟨2 * aux_prop_uniform_resolvent_cutoff_oscillation_Kinst d epsilon (qs) (max Kmu 0)
    (V1 * max Kmu 0) (max Cc 0) (max Ch 0), by unfold aux_prop_uniform_resolvent_cutoff_oscillation_Kinst; positivity, ?_⟩
  intro N lam hlam f x r hr0 hr1
  have hcoerN : ∀ v : killedSobolevGraph (centeredCube (qc) (qs) hr),
      ‖(v : SobolevData (centeredCube (qc) (qs) hr)).1‖ ^ 2 ≤ max Cc 0 * sobolevCoefficientForm (aN N) v.val v.val ∧
      globalFractionalSqNorm (3 / 4) (Set.indicator (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) (fun x => (v : SobolevData (centeredCube (qc) (qs) hr)).1 x)) ≤
        ENNReal.ofReal (max Cc 0 * sobolevCoefficientForm (aN N) v.val v.val) := by
    intro v
    have hE0 : 0 ≤ sobolevCoefficientForm (aN N) v.val v.val := sobolevCoefficientForm_nonneg _ _
    have hmono : Kcoer N * sobolevCoefficientForm (aN N) v.val v.val ≤
        max Cc 0 * sobolevCoefficientForm (aN N) v.val v.val :=
      mul_le_mul_of_nonneg_right (hKc N) hE0
    have h := hcoer N v
    rw [hE] at h
    exact ⟨h.1.trans hmono, h.2.trans (ENNReal.ofReal_le_ofReal hmono)⟩
  have hHolN : ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 → ∀ MF : ℝ, 0 ≤ MF →
      (∀ x ∈ (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), |F0 x| ≤ MF) → ∀ v : killedSobolevGraph (centeredCube (qc) (qs) hr),
        (∀ w : killedSobolevGraph (centeredCube (qc) (qs) hr), sobolevCoefficientForm (aN N) v.val w.val =
          ∫ x in (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), F0 x * (w : SobolevData (centeredCube (qc) (qs) hr)).1 x) →
        ∃ vc : C(SpatialCoordinates d, ℝ),
          (((v : SobolevData (centeredCube (qc) (qs) hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d))] vc) ∧
          (∀ x ∉ (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), vc x = 0) ∧
          (∀ x ∈ closure (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), ∀ y ∈ closure (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)),
            |vc x - vc y| ≤ max Ch 0 * MF * dist x y ^ (1 / 2 : ℝ)) := by
    intro F0 hF0 MF hMF hF0b v hv
    have hv' : ∀ w : killedSobolevGraph (centeredCube (qc) (qs) hr),
        E N v w = ∫ x in (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), F0 x * (w : SobolevData (centeredCube (qc) (qs) hr)).1 x := by
      intro w; rw [hE]; exact hv w
    obtain ⟨vc, h1, h2, h3⟩ := hHolder N F0 hF0 MF hMF hF0b v hv'
    refine ⟨vc, h1, h2, fun x hx y hy => (h3 x hx y hy).trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg _)
    exact mul_le_mul_of_nonneg_right (hKh N) hMF
  have hfin : ∀ w : killedSobolevGraph (centeredCube (qc) (qs) hr), sobolevCoefficientForm (aN N) (uN N lam f).val w.val =
      ∫ x in (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)), (f x - lam * RN N lam f x) * (w : SobolevData (centeredCube (qc) (qs) hr)).1 x ∂(muN N) := by
    intro w; rw [← hE]; exact hfinite N lam hlam f w
  have hh : AEStronglyMeasurable (fun x => f x - lam * RN N lam f x) ((muN N).restrict (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d))) :=
    (f.continuous.aestronglyMeasurable.sub
      ((hRNmeas N lam hlam f).const_mul lam).aestronglyMeasurable)
  have hmain := aux_mfd_prop_as_forms_osc_instance hd epsilon hepsilon hε1 qc qs hr (muN N) (hac N) (max Kmu 0)
    (V1 * max Kmu 0) (max Cc 0) (max Ch 0) hKm0 (mul_nonneg hV1 hKm0) hKc0 hKh0 (hgrowthN N)
    (hV N) (aN N) hcoerN hHolN (uN N lam f) (fun x => f x - lam * RN N lam f x) hh (2 * ‖f‖)
    (by positivity) (hsource N lam hlam f) hfin (uN0 N lam f) (hzero N lam f) x r hr0 hr1
  refine hmain.trans (le_of_eq ?_)
  ring


theorem aux_mfd_prop_as_forms_smooth_memLp {d : ℕ}
    (qc : SpatialCoordinates d) (qs : ℝ) (hr : 0 < qs)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure (centeredCube qc qs hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (f : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ ∞ f) : MemLp f 2 ν :=
  aux_prop_uniform_resolvent_ident_memLp_of_continuous ν _
    (centeredCube_isBounded qc hr).isCompact_closure hsupp f hf.continuous

theorem aux_mfd_prop_as_forms_smooth_dense {d : ℕ} (hd : 2 ≤ d)
    (qc : SpatialCoordinates d) (qs : ℝ) (hr : 0 < qs)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure (centeredCube qc qs hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (u : CubeFractionalL2 (k := 1) hd qc qs hr halfFractionalOrder) :
    ∃ (a : ℕ → CubeFractionalL2 (k := 1) hd qc qs hr halfFractionalOrder)
      (f : ℕ → SpatialCoordinates d → ℝ)
      (w : ℕ → CubeFractionalL2 (k := 1) hd qc qs hr halfFractionalOrder),
      (∀ n, ContDiff ℝ ∞ (f n)) ∧ (∀ n, MemLp (f n) 2 ν) ∧
      (∀ n, (a n).val 0 =ᵐ[volume.restrict (centeredCube qc qs hr : Set (SpatialCoordinates d))] f n) ∧
      (∀ n, (w n).val 0 = u.val 0 - (a n).val 0) ∧
      Tendsto (fun n => cubeFractionalL2Norm hd qc qs hr halfFractionalOrder (w n)) atTop (𝓝 0) := by
  obtain ⟨a, f, w, hsm, hae, hv, ht⟩ := lem_19_smooth_density d hd qc qs hr u
  exact ⟨a, f, w, hsm, fun n => aux_mfd_prop_as_forms_smooth_memLp qc qs hr ν hsupp (f n) (hsm n), hae, hv, ht⟩

theorem aux_mfd_prop_as_forms_trace_smooth_lin {d : ℕ} (hd : 2 ≤ d)
    (qc : SpatialCoordinates d) (qs : ℝ)
    (hr : 0 < qs)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))))ᶜ = 0) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (qc)
      (qs) hr halfFractionalOrder → Lp ℝ 2 ν)
    (hT : SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr ν K C T) (c : ℝ)
    (a b e : CubeFractionalL2 (k := 1) hd (qc)
      (qs) hr halfFractionalOrder)
    (f g : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (ha : (a.val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube (qc) (qs) hr :
        Set (SpatialCoordinates d))] f)
    (hb : (b.val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube (qc) (qs) hr :
        Set (SpatialCoordinates d))] g)
    (he : (e.val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube (qc) (qs) hr :
        Set (SpatialCoordinates d))] fun x => c * f x + g x) :
    T e = c • T a + T b := by
  have hfm := aux_mfd_prop_as_forms_smooth_memLp qc qs hr ν hsupp f hf
  have hgm := aux_mfd_prop_as_forms_smooth_memLp qc qs hr ν hsupp g hg
  have hsm : ContDiff ℝ ∞ (fun x => c * f x + g x) := (contDiff_const.mul hf).add hg
  have hem := aux_mfd_prop_as_forms_smooth_memLp qc qs hr ν hsupp _ hsm
  rw [hT.2.2 f hf a ha hfm, hT.2.2 g hg b hb hgm, hT.2.2 _ hsm e he hem,
    ← MemLp.toLp_const_smul c hfm, ← MemLp.toLp_add (hfm.const_smul c) hgm]
  exact MemLp.toLp_congr hem _ (Eventually.of_forall fun x => by simp)

theorem aux_mfd_prop_as_forms_trace_tendsto {d : ℕ} (hd : 2 ≤ d)
    (qc : SpatialCoordinates d) (qs : ℝ)
    (hr : 0 < qs)
    (ν : Measure (SpatialCoordinates d)) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (qc)
      (qs) hr halfFractionalOrder → Lp ℝ 2 ν)
    (hT : SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr ν K C T)
    (x : CubeFractionalL2 (k := 1) hd (qc)
      (qs) hr halfFractionalOrder)
    (y δ : ℕ → CubeFractionalL2 (k := 1) hd (qc)
      (qs) hr halfFractionalOrder)
    (hδ : ∀ n, (δ n).val 0 = x.val 0 - (y n).val 0)
    (hlim : Tendsto (fun n => cubeFractionalL2Norm hd (qc)
      (qs) hr halfFractionalOrder (δ n)) atTop (𝓝 0)) :
    Tendsto (fun n => T (y n)) atTop (𝓝 (T x)) := by
  set Lc := C * (K + (ν (closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))))).toReal) with hLc
  set L := max 1 Lc with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLL : Lc ≤ L ^ 2 := by
    have : L ≤ L ^ 2 := by nlinarith
    exact (le_max_right _ _).trans this
  have hbd : ∀ n, ‖T (y n) - T x‖ ≤ L * cubeFractionalL2Norm hd (qc)
      (qs) hr halfFractionalOrder (δ n) := by
    intro n
    have hN := aux_prop_speed_resolvent_norm_nonneg hd (qc)
      (qs) hr halfFractionalOrder (δ n)
    have h := hT.2.1 x (y n) (δ n) (hδ n)
    have hsq : ‖T x - T (y n)‖ ^ 2 ≤ (L * cubeFractionalL2Norm hd (qc)
        (qs) hr halfFractionalOrder (δ n)) ^ 2 := by
      calc ‖T x - T (y n)‖ ^ 2 ≤ _ := h
        _ ≤ L ^ 2 * (cubeFractionalL2Norm hd (qc)
            (qs) hr halfFractionalOrder (δ n)) ^ 2 :=
            mul_le_mul_of_nonneg_right hLL (sq_nonneg _)
        _ = _ := by ring
    rw [norm_sub_rev]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (by linarith) hN) two_ne_zero).1 hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) hbd ?_
  simpa using hlim.const_mul L

theorem aux_mfd_prop_as_forms_trace_linear {d : ℕ} (hd : 2 ≤ d)
    (qc : SpatialCoordinates d) (qs : ℝ)
    (hr : 0 < qs)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))))ᶜ = 0) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (qc)
      (qs) hr halfFractionalOrder → Lp ℝ 2 ν)
    (hT : SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr ν K C T) (c : ℝ)
    (u v w : CubeFractionalL2 (k := 1) hd (qc)
      (qs) hr halfFractionalOrder)
    (hw : w.val 0 = c • u.val 0 + v.val 0) :
    T w = c • T u + T v := by
  obtain ⟨a, f, wa, hf, -, hfa, hwa, hwalim⟩ :=
    aux_mfd_prop_as_forms_smooth_dense hd qc qs hr ν hsupp u
  obtain ⟨b, g, wb, hg, -, hgb, hwb, hwblim⟩ :=
    aux_mfd_prop_as_forms_smooth_dense hd qc qs hr ν hsupp v
  choose e he1 he2 using fun n => aux_prop_speed_resolvent_frac_lincomb hd
    (qc) (qs) hr halfFractionalOrder
    c (a n) (b n)
  have hTe : ∀ n, T (e n) = c • T (a n) + T (b n) := by
    intro n
    refine aux_mfd_prop_as_forms_trace_smooth_lin hd qc qs hr ν hsupp K C T hT c (a n) (b n) (e n)
      (f n) (g n) (hf n) (hg n) (hfa n) (hgb n) ?_
    rw [he1 n]
    filter_upwards [Lp.coeFn_add (c • (a n).val 0) ((b n).val 0),
      Lp.coeFn_smul c ((a n).val 0), hfa n, hgb n] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
  choose dd hdd1 hdd2 using fun n => aux_prop_speed_resolvent_frac_lincomb hd
    (qc) (qs) hr halfFractionalOrder
    c (wa n) (wb n)
  have hddv : ∀ n, (dd n).val 0 = w.val 0 - (e n).val 0 := by
    intro n
    rw [hdd1 n, hwa n, hwb n, hw, he1 n, smul_sub]
    abel
  have hddlim : Tendsto (fun n => cubeFractionalL2Norm hd (qc)
      (qs) hr halfFractionalOrder (dd n)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => aux_prop_speed_resolvent_norm_nonneg hd _ _ hr _ (dd n))
      hdd2 ?_
    simpa using (hwalim.const_mul |c|).add hwblim
  have hL1 := aux_mfd_prop_as_forms_trace_tendsto hd qc qs hr ν K C T hT u a wa hwa hwalim
  have hL2 := aux_mfd_prop_as_forms_trace_tendsto hd qc qs hr ν K C T hT v b wb hwb hwblim
  have hL3 := aux_mfd_prop_as_forms_trace_tendsto hd qc qs hr ν K C T hT w e dd hddv hddlim
  have hlim2 : Tendsto (fun n => T (e n)) atTop (𝓝 (c • T u + T v)) := by
    simp_rw [hTe]
    exact (hL1.const_smul c).add hL2
  exact tendsto_nhds_unique hL3 hlim2

open Classical in
theorem aux_mfd_prop_as_forms_A_lin {d : ℕ} (hd : 2 ≤ d)
    (qc : SpatialCoordinates d) (qs : ℝ)
    (hr : 0 < qs)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))))ᶜ = 0) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (qc)
      (qs) hr halfFractionalOrder → Lp ℝ 2 ν)
    (hT : SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr ν K C T)
    (E : DomainL2 (centeredCube (qc)
      (qs) hr) → ℝ≥0∞)
    (hclosed : ∀ (c : ℝ) (w1 w2 : DomainL2 (centeredCube (qc)
      (qs) hr)), E w1 ≠ ⊤ → E w2 ≠ ⊤ → E (c • w1 + w2) ≠ ⊤)
    (i : (u : DomainL2 (centeredCube (qc)
        (qs) hr)) → E u ≠ ⊤ →
      CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder)
    (hi0 : ∀ (u : DomainL2 (centeredCube (qc)
      (qs) hr)) (hu : E u ≠ ⊤), (i u hu).val 0 = u)
    (c : ℝ) (w1 w2 : DomainL2 (centeredCube (qc)
      (qs) hr)) (h1 : E w1 ≠ ⊤) (h2 : E w2 ≠ ⊤) :
    (if h : E (c • w1 + w2) ≠ ⊤ then T (i (c • w1 + w2) h) else 0) =
      c • (if h : E w1 ≠ ⊤ then T (i w1 h) else 0) +
        (if h : E w2 ≠ ⊤ then T (i w2 h) else 0) := by
  rw [dite_eq_left (hclosed c w1 w2 h1 h2), dite_eq_left h1, dite_eq_left h2]
  exact aux_mfd_prop_as_forms_trace_linear hd qc qs hr ν hsupp K C T hT c _ _ _
    (by rw [hi0, hi0, hi0])

theorem aux_mfd_prop_as_forms_parts_AB {d : ℕ} (hd : 2 ≤ d)
    (qc : SpatialCoordinates d) (qs : ℝ) (hr : 0 < qs)
    (G : DomainL2 (centeredCube (qc) (qs) hr) →L[ℝ]
      DomainL2 (centeredCube (qc) (qs) hr))
    (Elim : DomainL2 (centeredCube (qc) (qs) hr) → ℝ≥0∞)
    (hElim : ∀ u : DomainL2 (centeredCube (qc) (qs) hr),
      Elim u = (limitFormEnergy G u).toENNReal)
    (mu muFull : Measure (SpatialCoordinates d))
    (hmu : mu = muFull.restrict
      (closure (centeredCube (qc) (qs) hr :
        Set (SpatialCoordinates d))))
    (hmufin : mu univ < ⊤) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (qc) (qs) hr
      halfFractionalOrder → Lp ℝ 2 mu)
    (hT : SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr mu K C T)
    (i : (u : DomainL2 (centeredCube (qc) (qs) hr)) →
      Elim u ≠ ⊤ →
      CubeFractionalL2 (k := 1) hd (qc) (qs) hr
        halfFractionalOrder)
    (hi : ∀ (u : DomainL2 (centeredCube (qc) (qs) hr))
      (hu : Elim u ≠ ⊤), (i u hu).val 0 = u)
    (J : DomainL2 (centeredCube (qc) (qs) hr) →
      SpatialCoordinates d → ℝ)
    (hJ : ∀ (u : DomainL2 (centeredCube (qc) (qs) hr))
      (hu : Elim u ≠ ⊤), (J u) =ᵐ[mu] (T (i u hu) : SpatialCoordinates d → ℝ))
    (hcoer : ∃ Ccoer : ℝ, 0 < Ccoer ∧
      ∀ w : DomainL2 (centeredCube (qc) (qs) hr),
        ENNReal.ofReal (‖w‖ ^ 2) ≤ ENNReal.ofReal Ccoer * Elim w)
    (hE0 : Elim 0 = 0)
    (hclosed : ∀ (c : ℝ)
      (w1 w2 : DomainL2 (centeredCube (qc) (qs) hr)),
      Elim w1 ≠ ⊤ → Elim w2 ≠ ⊤ → Elim (c • w1 + w2) ≠ ⊤)
    (hpara : ∀ (w1 w2 : DomainL2 (centeredCube (qc) (qs) hr)),
      Elim w1 ≠ ⊤ → Elim w2 ≠ ⊤ →
      (Elim (w1 + w2)).toReal + (Elim (w1 - w2)).toReal =
        2 * (Elim w1).toReal + 2 * (Elim w2).toReal)
    (hscale : ∀ (c : ℝ)
      (u : DomainL2 (centeredCube (qc) (qs) hr)),
      Elim u ≠ ⊤ → Elim (c • u) = ENNReal.ofReal (c ^ 2) * Elim u)
    (Ktr : ℝ) (hKtr : 0 ≤ Ktr)
    (hJtr : ∀ (u : DomainL2 (centeredCube (qc) (qs) hr))
      (_hu : Elim u ≠ ⊤),
      (∫⁻ x, ENNReal.ofReal (J u x ^ 2) ∂mu) ≤ ENNReal.ofReal Ktr * Elim u)
    (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    ∃ ustar : DomainL2 (centeredCube (qc) (qs) hr),
      Elim ustar ≠ ⊤ ∧
      (∀ w : DomainL2 (centeredCube (qc) (qs) hr),
        Elim w ≠ ⊤ →
        (Elim ustar).toReal + lam * (∫ x, J ustar x ^ 2 ∂mu) -
            2 * ∫ x, f x * J ustar x ∂mu ≤
          (Elim w).toReal + lam * (∫ x, J w x ^ 2 ∂mu) -
            2 * ∫ x, f x * J w x ∂mu) ∧
      (∀ w : DomainL2 (centeredCube (qc) (qs) hr),
        Elim w ≠ ⊤ →
        (∀ v : DomainL2 (centeredCube (qc) (qs) hr),
          Elim v ≠ ⊤ →
          (Elim w).toReal + lam * (∫ x, J w x ^ 2 ∂mu) -
              2 * ∫ x, f x * J w x ∂mu ≤
            (Elim v).toReal + lam * (∫ x, J v x ^ 2 ∂mu) -
              2 * ∫ x, f x * J v x ∂mu) →
        w = ustar) := by
  have : IsFiniteMeasure mu := ⟨hmufin⟩
  have hsupp : mu (closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))))ᶜ = 0 := by
    rw [hmu, Measure.restrict_apply isClosed_closure.measurableSet.compl,
      Set.compl_inter_self, measure_empty]
  have hfm : MemLp (fun x => f x) 2 mu :=
    MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun x => f.norm_coe_le_norm x)
  let A : DomainL2 (centeredCube (qc) (qs) hr) → Lp ℝ 2 mu :=
    fun w => if h : Elim w ≠ ⊤ then T (i w h) else 0
  have hAw : ∀ (w : DomainL2 (centeredCube (qc) (qs) hr))
      (hw : Elim w ≠ ⊤), A w = T (i w hw) := fun w hw => dite_eq_left hw
  have hlsc : LowerSemicontinuous Elim := by
    have hE : Elim = fun u => (limitFormEnergy G u).toENNReal := funext hElim
    rw [hE]
    exact aux_prop_speed_resolvent_elim_lsc G
  have hAlin : ∀ (c : ℝ)
      (w1 w2 : DomainL2 (centeredCube (qc) (qs) hr)),
      Elim w1 ≠ ⊤ → Elim w2 ≠ ⊤ → A (c • w1 + w2) = c • A w1 + A w2 :=
    fun c w1 w2 h1 h2 =>
      aux_mfd_prop_as_forms_A_lin hd qc qs hr mu hsupp K C T hT Elim hclosed i hi c w1 w2 h1 h2
  have hAbd : ∀ w : DomainL2 (centeredCube (qc) (qs) hr),
      Elim w ≠ ⊤ → ‖A w‖ ^ 2 ≤ Ktr * (Elim w).toReal := by
    intro w hw
    rw [hAw w hw]
    exact aux_prop_speed_resolvent_trace_bound (J w) _ (hJ w hw) Ktr hKtr _ hw (hJtr w hw)
  obtain ⟨ustar, hus, hmin, huniq⟩ :=
    aux_prop_speed_resolvent_abstract_min Elim A (hfm.toLp (fun x => f x)) lam hlam hlsc hE0
      hclosed hpara hscale hcoer hAlin Ktr hKtr hAbd
  have key : ∀ (w : DomainL2 (centeredCube (qc) (qs) hr))
      (hw : Elim w ≠ ⊤),
      (Elim w).toReal + lam * (∫ x, J w x ^ 2 ∂mu) - 2 * ∫ x, f x * J w x ∂mu =
        (Elim w).toReal + lam * ‖A w‖ ^ 2 -
          2 * ⟪hfm.toLp (fun x => f x), A w⟫_ℝ := by
    intro w hw
    have hJA : J w =ᵐ[mu] ⇑(A w) := by
      rw [hAw w hw]
      exact hJ w hw
    rw [aux_prop_speed_resolvent_sq_integral_congr (J w) (A w) hJA,
      aux_prop_speed_resolvent_f_integral_inner f hfm (J w) (A w) hJA]
  refine ⟨ustar, hus, fun w hw => ?_, fun w hw hwmin => ?_⟩
  · rw [key ustar hus, key w hw]
    exact hmin w hw
  · exact huniq w hw (fun v hv => by
      rw [← key w hw, ← key v hv]
      exact hwmin v hv)


theorem aux_mfd_prop_as_forms_ident_trace_passage {d : ℕ} (hd : 2 ≤ d)
    (qc : SpatialCoordinates d) (qs : ℝ) (hr : 0 < qs)
    (SInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (ν : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    [IsFiniteMeasure μ]
    (hμsupp : μ (closure (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (Kμ Mbar : ℝ) (hKμ : 0 ≤ Kμ)
    (hνfin : ∀ k, ν k univ < ⊤)
    (hνsupp : ∀ k, ν k (closure (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (hνmass : ∀ k, (ν k (closure (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d)))).toReal ≤ Mbar)
    (hνgrowth : ∀ k, ∀ x ∈ closure (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 → ν k (ball x rr) ≤ ENNReal.ofReal (Kμ * rr ^ t))
    (hνdens : ∀ k, ∃ D : ℝ, 0 ≤ D ∧ ν k ≤ ENNReal.ofReal D •
      volume.restrict (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d)))
    (hW : ∀ h : SpatialCoordinates d → ℝ, Continuous h →
      Tendsto (fun k => ∫ x, h x ∂(ν k)) atTop (𝓝 (∫ x, h x ∂μ)))
    (T : CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder → Lp ℝ 2 μ)
    (Ktr Ctr : ℝ) (hKtr : 0 ≤ Ktr) (hCtr : 0 ≤ Ctr)
    (hT : SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr μ Ktr Ctr T)
    (s : ℕ → DomainL2 (centeredCube (qc)
      (qs) hr))
    (z : CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder)
    (hs : Tendsto s atTop (𝓝 (z.val 0)))
    (w3 : ℕ → CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder)
    (hw3 : ∀ k, (w3 k).val 0 = s k) (B : ℝ)
    (hB : ∀ k, cubeFractionalL2Norm hd (qc)
      (qs) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder (w3 k) ≤ B)
    (ψ : SpatialCoordinates d → ℝ) (hψ : Continuous ψ) :
    Tendsto (fun k => ∫ x, (s k x - ψ x) ^ 2 ∂(ν k)) atTop
      (𝓝 (∫ x, (T z x - ψ x) ^ 2 ∂μ)) := by
  set Qs : Set (SpatialCoordinates d) := (centeredCube (qc)
    (qs) hr : Set (SpatialCoordinates d)) with hQs
  have hQeq : Qs = (centeredCube qc qs hr : Set (SpatialCoordinates d)) := (rfl : (centeredCube qc qs hr : Set (SpatialCoordinates d)) = _)
  have hKc : IsCompact (closure Qs) := (centeredCube_isBounded (qc) hr).isCompact_closure
  have hνfinI : ∀ k, IsFiniteMeasure (ν k) := fun k => ⟨hνfin k⟩
  obtain ⟨⟨C, hC0, htr⟩, hinterp⟩ := lem_19 d hd SInterp (qc) (qs) hr t ht
  -- finite-cutoff traces: identity on `H^{1/2}` elements, one Lipschitz constant
  have hTk : ∀ k, ∃ Tk : CubeFractionalL2 (k := 1) hd (qc) (qs) hr halfFractionalOrder →
      Lp ℝ 2 (ν k),
      (∀ (u v w : CubeFractionalL2 (k := 1) hd (qc) (qs) hr halfFractionalOrder),
        w.val 0 = u.val 0 - v.val 0 →
        ‖Tk u - Tk v‖ ^ 2 ≤ C * (Kμ + (ν k (closure Qs)).toReal) *
          (cubeFractionalL2Norm hd (qc) (qs) hr halfFractionalOrder w) ^ 2) ∧
      (∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
        ∀ (v : CubeFractionalL2 (k := 1) hd (qc) (qs) hr halfFractionalOrder),
          (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Qs] f →
          ∀ hf : MemLp f 2 (ν k), Tk v = hf.toLp f) ∧
      (∀ u : CubeFractionalL2 (k := 1) hd (qc) (qs) hr halfFractionalOrder,
        MemLp (u.val 0) 2 (ν k) ∧ ∀ hu : MemLp (u.val 0) 2 (ν k), Tk u = hu.toLp (u.val 0)) := by
    intro k
    obtain ⟨D, hD0, hD⟩ := hνdens k
    obtain ⟨Tk, ⟨_, hlip, hsm, _, hden⟩, _⟩ :=
      htr (ν k) Kμ (hνfin k) (hνsupp k) hKμ (hνgrowth k)
    exact ⟨Tk, hlip, hsm, hden D hD0 hD⟩
  choose Tk hTk_lip hTk_sm hTk_id using hTk
  -- interpolation upgrade
  obtain ⟨vhalf, hvhalf, diff, hdiff, hdiff0⟩ :=
    hinterp _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder rfl w3 (z.val 0) B hB
      (by simpa only [hw3] using hs)
  -- smooth approximation of `z` for the limit measure
  have hμsupp' : μ (closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))))ᶜ = 0 := by
    rw [← hQeq]; exact hμsupp
  obtain ⟨a, f, w, hfsm, hfLp, haf, hw, hw0⟩ :=
    aux_mfd_prop_as_forms_smooth_dense hd qc qs hr μ hμsupp' z
  -- `H^{1/2}` elements with prescribed first coordinate
  obtain ⟨zero, hzero⟩ := hT.1 z z
  obtain ⟨neg, hneg⟩ := hT.1 zero z
  have hS : ∀ k, ∃ Sk : CubeFractionalL2 (k := 1) hd (qc) (qs) hr halfFractionalOrder,
      Sk.val 0 = s k := by
    intro k
    obtain ⟨Sk, hSk⟩ := hT.1 (diff k) neg
    refine ⟨Sk, ?_⟩
    rw [hSk, hdiff k, hneg, hzero, hw3 k]
    abel
  choose S hSval using hS
  -- constants
  set L : ℝ := Real.sqrt (C * (Kμ + Mbar)) with hLdef
  set Lμ : ℝ := Real.sqrt (Ctr * (Ktr + (μ (closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))))).toReal))
    with hLμdef
  have hMbar : ∀ k, 0 ≤ Kμ + Mbar := fun k => by
    have := hνmass k
    have : 0 ≤ (ν k (closure Qs)).toReal := ENNReal.toReal_nonneg
    linarith
  have hlipk : ∀ k (u v w' : CubeFractionalL2 (k := 1) hd (qc) (qs) hr halfFractionalOrder),
      w'.val 0 = u.val 0 - v.val 0 →
      ‖Tk k u - Tk k v‖ ≤ L * |cubeFractionalL2Norm hd (qc) (qs) hr halfFractionalOrder w'| := by
    intro k u v w' hw'
    refine aux_prop_uniform_resolvent_ident_le_sqrt_mul _ _ _ (norm_nonneg _)
      (mul_nonneg hC0 (hMbar k)) ?_
    refine (hTk_lip k u v w' hw').trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ hC0
    linarith [hνmass k]
  have hlipμ : ∀ (u v w' : CubeFractionalL2 (k := 1) hd (qc) (qs) hr halfFractionalOrder),
      w'.val 0 = u.val 0 - v.val 0 →
      ‖T u - T v‖ ≤ Lμ * |cubeFractionalL2Norm hd (qc) (qs) hr halfFractionalOrder w'| := by
    intro u v w' hw'
    refine aux_prop_uniform_resolvent_ident_le_sqrt_mul _ _ _ (norm_nonneg _)
      (mul_nonneg hCtr (add_nonneg hKtr ENNReal.toReal_nonneg)) ?_
    exact hT.2.1 u v w' hw'
  -- `L²` representatives
  have hψk : ∀ k, MemLp ψ 2 (ν k) := fun k =>
    aux_prop_uniform_resolvent_ident_memLp_of_continuous (ν k) (closure Qs) hKc (hνsupp k) ψ hψ
  have hψμ : MemLp ψ 2 μ :=
    aux_prop_uniform_resolvent_ident_memLp_of_continuous μ (closure Qs) hKc hμsupp ψ hψ
  have hfk : ∀ n k, MemLp (f n) 2 (ν k) := fun n k =>
    aux_prop_uniform_resolvent_ident_memLp_of_continuous (ν k) (closure Qs) hKc (hνsupp k) (f n)
      (hfsm n).continuous
  -- the quantities
  set X : ℕ → ℝ := fun k => ‖Tk k (S k) - (hψk k).toLp ψ‖ with hXdef
  set Y : ℝ := ‖T z - hψμ.toLp ψ‖ with hYdef
  set e : ℕ → ℕ → ℝ := fun n k =>
    ‖Tk k (a n) - (hψk k).toLp ψ‖ - ‖T (a n) - hψμ.toLp ψ‖ with hedef
  have hbound : ∀ n k, |X k - Y| ≤
      L * |cubeFractionalL2Norm hd (qc) (qs) hr halfFractionalOrder (diff k)| +
        (L + Lμ) * |cubeFractionalL2Norm hd (qc) (qs) hr halfFractionalOrder (w n)| + |e n k| := by
    intro n k
    have h1 : ‖Tk k (S k) - Tk k z‖ ≤
        L * |cubeFractionalL2Norm hd (qc) (qs) hr halfFractionalOrder (diff k)| :=
      hlipk k (S k) z (diff k) (by rw [hdiff k, hSval k, hw3 k])
    have h2 : ‖Tk k z - Tk k (a n)‖ ≤
        L * |cubeFractionalL2Norm hd (qc) (qs) hr halfFractionalOrder (w n)| :=
      hlipk k z (a n) (w n) (hw n)
    have h3 : ‖T z - T (a n)‖ ≤
        Lμ * |cubeFractionalL2Norm hd (qc) (qs) hr halfFractionalOrder (w n)| :=
      hlipμ z (a n) (w n) (hw n)
    have t1 : |X k - ‖Tk k (a n) - (hψk k).toLp ψ‖| ≤ ‖Tk k (S k) - Tk k (a n)‖ := by
      have := abs_norm_sub_norm_le (Tk k (S k) - (hψk k).toLp ψ) (Tk k (a n) - (hψk k).toLp ψ)
      simpa [hXdef, sub_sub_sub_cancel_right] using this
    have t2 : ‖Tk k (S k) - Tk k (a n)‖ ≤ ‖Tk k (S k) - Tk k z‖ + ‖Tk k z - Tk k (a n)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have t3 : |‖T (a n) - hψμ.toLp ψ‖ - Y| ≤ ‖T z - T (a n)‖ := by
      have := abs_norm_sub_norm_le (T (a n) - hψμ.toLp ψ) (T z - hψμ.toLp ψ)
      rw [sub_sub_sub_cancel_right, norm_sub_rev (T (a n)) (T z)] at this
      exact this
    have hsplit : X k - Y = (X k - ‖Tk k (a n) - (hψk k).toLp ψ‖) + e n k +
        (‖T (a n) - hψμ.toLp ψ‖ - Y) := by
      simp only [hedef]; ring
    rw [hsplit]
    calc |(X k - ‖Tk k (a n) - (hψk k).toLp ψ‖) + e n k + (‖T (a n) - hψμ.toLp ψ‖ - Y)|
        ≤ |X k - ‖Tk k (a n) - (hψk k).toLp ψ‖| + |e n k| + |‖T (a n) - hψμ.toLp ψ‖ - Y| :=
          abs_add_three _ _ _
      _ ≤ _ := by nlinarith [t1, t2, t3, h1, h2, h3]
  -- the smooth comparison term converges for each fixed `n`
  have he : ∀ n, Tendsto (e n) atTop (𝓝 0) := by
    intro n
    have hTkan : ∀ k, Tk k (a n) = (hfk n k).toLp (f n) := fun k =>
      hTk_sm k (f n) (hfsm n) (a n) (haf n) (hfk n k)
    have hTan : T (a n) = (hfLp n).toLp (f n) :=
      hT.2.2 (f n) (hfsm n) (a n) (haf n) (hfLp n)
    have hsqk : ∀ k, ‖Tk k (a n) - (hψk k).toLp ψ‖ =
        Real.sqrt (∫ x, (f n x - ψ x) ^ 2 ∂(ν k)) := by
      intro k
      rw [← aux_prop_uniform_resolvent_ident_norm_sub_sq (Tk k (a n)) ((hψk k).toLp ψ) (f n) ψ
        (by rw [hTkan k]; exact MemLp.coeFn_toLp _) (MemLp.coeFn_toLp _),
        Real.sqrt_sq (norm_nonneg _)]
    have hsqμ : ‖T (a n) - hψμ.toLp ψ‖ = Real.sqrt (∫ x, (f n x - ψ x) ^ 2 ∂μ) := by
      rw [← aux_prop_uniform_resolvent_ident_norm_sub_sq (T (a n)) (hψμ.toLp ψ) (f n) ψ
        (by rw [hTan]; exact MemLp.coeFn_toLp _) (MemLp.coeFn_toLp _),
        Real.sqrt_sq (norm_nonneg _)]
    have hcont : Continuous (fun x => (f n x - ψ x) ^ 2) :=
      ((hfsm n).continuous.sub hψ).pow 2
    have hlim := (hW _ hcont).sqrt
    have h2 : Tendsto (fun k => Real.sqrt (∫ x, (f n x - ψ x) ^ 2 ∂(ν k)) -
        Real.sqrt (∫ x, (f n x - ψ x) ^ 2 ∂μ)) atTop (𝓝 0) := by
      have := hlim.sub_const (Real.sqrt (∫ x, (f n x - ψ x) ^ 2 ∂μ))
      rwa [sub_self] at this
    refine h2.congr (fun k => ?_)
    simp only [hedef, hsqk, hsqμ]
  have hdiffabs : Tendsto (fun k => L * |cubeFractionalL2Norm hd (qc) (qs) hr halfFractionalOrder
      (diff k)|) atTop (𝓝 0) := by
    simpa using (hdiff0.abs).const_mul L
  have hwabs : Tendsto (fun n => (L + Lμ) * |cubeFractionalL2Norm hd (qc) (qs) hr halfFractionalOrder
      (w n)|) atTop (𝓝 0) := by
    simpa using (hw0.abs).const_mul (L + Lμ)
  have hXY : Tendsto X atTop (𝓝 Y) :=
    aux_prop_uniform_resolvent_ident_eps3 X Y e _ _ hbound hwabs hdiffabs he
  -- back to integrals
  have hXsq : ∀ k, X k ^ 2 = ∫ x, (s k x - ψ x) ^ 2 ∂(ν k) := by
    intro k
    obtain ⟨hmem, hid⟩ := hTk_id k (S k)
    refine aux_prop_uniform_resolvent_ident_norm_sub_sq _ _ _ ψ ?_ (MemLp.coeFn_toLp _)
    rw [hid hmem]
    refine (MemLp.coeFn_toLp hmem).trans ?_
    rw [hSval k]
  have hYsq : Y ^ 2 = ∫ x, (T z x - ψ x) ^ 2 ∂μ :=
    aux_prop_uniform_resolvent_ident_norm_sub_sq _ _ _ ψ (Filter.EventuallyEq.refl _ _)
      (MemLp.coeFn_toLp _)
  rw [← hYsq]
  exact (hXY.pow 2).congr hXsq

theorem aux_mfd_prop_as_forms_ident_functional_passage {d : ℕ} (hd : 2 ≤ d)
    (qc : SpatialCoordinates d) (qs : ℝ) (hr : 0 < qs)
    (SInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (ν : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    [IsFiniteMeasure μ]
    (hμsupp : μ (closure (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (Kμ Mbar : ℝ) (hKμ : 0 ≤ Kμ)
    (hνfin : ∀ k, ν k univ < ⊤)
    (hνsupp : ∀ k, ν k (closure (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (hνmass : ∀ k, (ν k (closure (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d)))).toReal ≤ Mbar)
    (hνgrowth : ∀ k, ∀ x ∈ closure (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 → ν k (ball x rr) ≤ ENNReal.ofReal (Kμ * rr ^ t))
    (hνdens : ∀ k, ∃ D : ℝ, 0 ≤ D ∧ ν k ≤ ENNReal.ofReal D •
      volume.restrict (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d)))
    (hW : ∀ h : SpatialCoordinates d → ℝ, Continuous h →
      Tendsto (fun k => ∫ x, h x ∂(ν k)) atTop (𝓝 (∫ x, h x ∂μ)))
    (T : CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder → Lp ℝ 2 μ)
    (Ktr Ctr : ℝ) (hKtr : 0 ≤ Ktr) (hCtr : 0 ≤ Ctr)
    (hT : SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr μ Ktr Ctr T)
    (s : ℕ → DomainL2 (centeredCube (qc)
      (qs) hr))
    (z : CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder)
    (hs : Tendsto s atTop (𝓝 (z.val 0)))
    (w3 : ℕ → CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder)
    (hw3 : ∀ k, (w3 k).val 0 = s k) (B : ℝ)
    (hB : ∀ k, cubeFractionalL2Norm hd (qc)
      (qs) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder (w3 k) ≤ B)
    (lam : ℝ) (F : SpatialCoordinates d → ℝ) (hF : Continuous F) :
    Tendsto (fun k => lam * ∫ x, (s k x) ^ 2 ∂(ν k) - 2 * ∫ x, F x * s k x ∂(ν k)) atTop
      (𝓝 (lam * ∫ x, (T z x) ^ 2 ∂μ - 2 * ∫ x, F x * T z x ∂μ)) := by
  have hKc : IsCompact (closure (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d))) :=
    (centeredCube_isBounded (qc) hr).isCompact_closure
  have : ∀ k, IsFiniteMeasure (ν k) := fun k => ⟨hνfin k⟩
  have h0 := aux_mfd_prop_as_forms_ident_trace_passage hd qc qs hr SInterp t ht ν μ hμsupp
    Kμ Mbar hKμ hνfin hνsupp hνmass hνgrowth hνdens hW T Ktr Ctr hKtr hCtr hT s z hs w3 hw3 B hB
    (fun _ => 0) continuous_const
  have h1 := aux_mfd_prop_as_forms_ident_trace_passage hd qc qs hr SInterp t ht ν μ hμsupp
    Kμ Mbar hKμ hνfin hνsupp hνmass hνgrowth hνdens hW T Ktr Ctr hKtr hCtr hT s z hs w3 hw3 B hB
    F hF
  have h2 := hW (fun x => F x ^ 2) (hF.pow 2)
  simp only [sub_zero] at h0
  have hsk : ∀ k, MemLp (s k : SpatialCoordinates d → ℝ) 2 (ν k) := by
    intro k
    obtain ⟨D, _, hD⟩ := hνdens k
    exact (Lp.memLp _).of_measure_le_smul ENNReal.ofReal_ne_top hD
  have hFk : ∀ k, MemLp F 2 (ν k) := fun k =>
    aux_prop_uniform_resolvent_ident_memLp_of_continuous (ν k) _ hKc (hνsupp k) F hF
  have hFμ : MemLp F 2 μ :=
    aux_prop_uniform_resolvent_ident_memLp_of_continuous μ _ hKc hμsupp F hF
  have heqk : ∀ k, lam * ∫ x, (s k x) ^ 2 ∂(ν k) - 2 * ∫ x, F x * s k x ∂(ν k) =
      lam * ∫ x, (s k x) ^ 2 ∂(ν k) - (∫ x, (s k x) ^ 2 ∂(ν k) + ∫ x, F x ^ 2 ∂(ν k) -
        ∫ x, (s k x - F x) ^ 2 ∂(ν k)) := by
    intro k
    rw [aux_prop_uniform_resolvent_ident_mul_eq (hsk k) (hFk k)]
    ring
  have heqμ : lam * ∫ x, (T z x) ^ 2 ∂μ - 2 * ∫ x, F x * T z x ∂μ =
      lam * ∫ x, (T z x) ^ 2 ∂μ - (∫ x, (T z x) ^ 2 ∂μ + ∫ x, F x ^ 2 ∂μ -
        ∫ x, (T z x - F x) ^ 2 ∂μ) := by
    rw [aux_prop_uniform_resolvent_ident_mul_eq (Lp.memLp (T z)) hFμ]
    ring
  rw [heqμ]
  exact ((h0.const_mul lam).sub ((h0.add h2).sub h1)).congr (fun k => (heqk k).symm)

theorem aux_mfd_prop_as_forms_ident_deterministic {d : ℕ} (hd : 2 ≤ d)
    (qc : SpatialCoordinates d) (qs : ℝ) (hr : 0 < qs)
    (SInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (a : ℕ → PositiveCoefficient (centeredCube (qc)
      (qs) hr))
    (EN : ℕ → DomainL2 (centeredCube (qc)
      (qs) hr) → ℝ≥0∞)
    (hEN : ∀ N u, EN N u = ⨅ v : {v : killedSobolevGraph (centeredCube
        (qc) (qs) hr) //
        (v : SobolevData (centeredCube (qc)
          (qs) hr)).1 = u},
      ENNReal.ofReal (sobolevCoefficientForm (a N)
        (v.val : SobolevData (centeredCube (qc)
          (qs) hr))
        (v.val : SobolevData (centeredCube (qc)
          (qs) hr))))
    (Elim : DomainL2 (centeredCube (qc)
      (qs) hr) → ℝ≥0∞)
    (hliminf : _root_.SubdiffusiveProcess.ResponseMoments.MoscoLiminf EN Elim) (hrec : _root_.SubdiffusiveProcess.ResponseMoments.MoscoRecovery EN Elim)
    (ν : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    [IsFiniteMeasure μ]
    (hμsupp : μ (closure (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (Kμ Mbar : ℝ) (hKμ : 0 ≤ Kμ)
    (hνfin : ∀ k, ν k univ < ⊤)
    (hνsupp : ∀ k, ν k (closure (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (hνmass : ∀ k, (ν k (closure (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d)))).toReal ≤ Mbar)
    (hνgrowth : ∀ k, ∀ x ∈ closure (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 → ν k (ball x rr) ≤ ENNReal.ofReal (Kμ * rr ^ t))
    (hνdens : ∀ k, ∃ D : ℝ, 0 ≤ D ∧ ν k ≤ ENNReal.ofReal D •
      volume.restrict (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d)))
    (hW : ∀ h : SpatialCoordinates d → ℝ, Continuous h →
      Tendsto (fun k => ∫ x, h x ∂(ν k)) atTop (𝓝 (∫ x, h x ∂μ)))
    (T : CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder → Lp ℝ 2 μ)
    (Ktr Ctr : ℝ) (hKtr : 0 ≤ Ktr) (hCtr : 0 ≤ Ctr)
    (hT : SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr μ Ktr Ctr T)
    (i : (u : DomainL2 (centeredCube (qc)
        (qs) hr)) → Elim u ≠ ⊤ →
      CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder)
    (hival : ∀ u (hu : Elim u ≠ ⊤), (i u hu).val 0 = u)
    (J : DomainL2 (centeredCube (qc)
      (qs) hr) → SpatialCoordinates d → ℝ)
    (hJ : ∀ u (hu : Elim u ≠ ⊤), J u =ᵐ[μ] (T (i u hu) : SpatialCoordinates d → ℝ))
    (lam : ℝ) (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (ustar : DomainL2 (centeredCube (qc)
      (qs) hr))
    (hmin : Elim ustar ≠ ⊤ ∧
      (∀ w, Elim w ≠ ⊤ →
        (Elim ustar).toReal + lam * (∫ x, (J ustar x) ^ 2 ∂μ) -
            2 * (∫ x, f x * J ustar x ∂μ) ≤
          (Elim w).toReal + lam * (∫ x, (J w x) ^ 2 ∂μ) - 2 * (∫ x, f x * J w x ∂μ)) ∧
      (∀ w, Elim w ≠ ⊤ →
        (∀ v, Elim v ≠ ⊤ →
          (Elim w).toReal + lam * (∫ x, (J w x) ^ 2 ∂μ) - 2 * (∫ x, f x * J w x ∂μ) ≤
            (Elim v).toReal + lam * (∫ x, (J v x) ^ 2 ∂μ) - 2 * (∫ x, f x * J v x ∂μ)) →
        w = ustar))
    (u : ℕ → killedSobolevGraph (centeredCube (qc)
      (qs) hr))
    (R : ℕ → SpatialCoordinates d → ℝ)
    (hRu : ∀ N, R N =ᵐ[volume.restrict (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d))]
      ((u N : SobolevData (centeredCube (qc)
        (qs) hr)).1 : SpatialCoordinates d → ℝ))
    (hweak : ∀ N (w : killedSobolevGraph (centeredCube (qc)
        (qs) hr)),
      sobolevCoefficientForm (a N)
          (u N : SobolevData (centeredCube (qc)
            (qs) hr))
          (w : SobolevData (centeredCube (qc)
            (qs) hr)) =
        ∫ x, (f x - lam * R N x) * (w : SobolevData (centeredCube
          (qc) (qs) hr)).1 x ∂(ν N))
    (henergy : ∀ N, sobolevCoefficientForm (a N)
        (u N : SobolevData (centeredCube (qc)
          (qs) hr))
        (u N : SobolevData (centeredCube (qc)
          (qs) hr)) ≤
      ‖f‖ ^ 2 * (ν N (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d))).toReal / lam)
    (Kc : ℕ → ℝ)
    (hcoer3 : ∀ N (v : killedSobolevGraph (centeredCube (qc)
        (qs) hr)),
      ∃ v3 : CubeFractionalL2 (k := 1) hd (qc)
          (qs) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
        v3.val 0 = (v : SobolevData (centeredCube (qc)
          (qs) hr)).1 ∧
        (cubeFractionalL2Norm hd (qc)
          (qs) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
          Kc N * sobolevCoefficientForm (a N)
            (v : SobolevData (centeredCube (qc)
              (qs) hr))
            (v : SobolevData (centeredCube (qc)
              (qs) hr)))
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (Mb : ℝ) (hMb : ∀ k, Kc (σ k) ≤ Mb)
    (ubar : DomainL2 (centeredCube (qc)
      (qs) hr))
    (hconv : Tendsto (fun k => (u (σ k) : SobolevData (centeredCube
      (qc) (qs) hr)).1) atTop
      (𝓝 ubar)) :
    ubar = ustar := by
  set Qs : Set (SpatialCoordinates d) := (centeredCube (qc)
    (qs) hr : Set (SpatialCoordinates d)) with hQs
  have hKc : IsCompact (closure Qs) :=
    (centeredCube_isBounded (qc) hr).isCompact_closure
  have : ∀ k, IsFiniteMeasure (ν k) := fun k => ⟨hνfin k⟩
  obtain ⟨hustar, hminle, huniq⟩ := hmin
  -- subsequence data
  have hWσ : ∀ h : SpatialCoordinates d → ℝ, Continuous h →
      Tendsto (fun k => ∫ x, h x ∂(ν (σ k))) atTop (𝓝 (∫ x, h x ∂μ)) := fun h hh =>
    (hW h hh).comp hσ.tendsto_atTop
  -- energy bound
  obtain ⟨Eb, hEb⟩ : ∃ Eb : ℝ, Eb = ‖f‖ ^ 2 * Mbar / lam := ⟨_, rfl⟩
  have hform_nn : ∀ N (v : killedSobolevGraph (centeredCube (qc)
      (qs) hr)),
      0 ≤ sobolevCoefficientForm (a N) (v : SobolevData _) (v : SobolevData _) :=
    fun N v => sobolevCoefficientForm_nonneg _ _
  have hEbN : ∀ N, sobolevCoefficientForm (a N) (u N : SobolevData _) (u N : SobolevData _)
      ≤ Eb := by
    intro N
    refine (henergy N).trans ?_
    have hm : (ν N Qs).toReal ≤ Mbar := by
      refine le_trans ?_ (hνmass N)
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono subset_closure)
    rw [hEb]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm (sq_nonneg _)) hlam.le
  have hENle : ∀ N (v : killedSobolevGraph (centeredCube (qc)
      (qs) hr)),
      EN N (v : SobolevData _).1 ≤
        ENNReal.ofReal (sobolevCoefficientForm (a N) (v : SobolevData _) (v : SobolevData _)) := by
    intro N v
    rw [hEN]
    exact iInf_le_of_le ⟨v, rfl⟩ le_rfl
  -- the cluster has finite limit energy
  have hubar : Elim ubar ≠ ⊤ := by
    have hle : Elim ubar ≤ ENNReal.ofReal Eb :=
      aux_prop_uniform_resolvent_ident_liminf_subseq EN Elim hliminf σ hσ _ ubar hconv _
        (Frequently.of_forall fun k =>
          (hENle (σ k) (u (σ k))).trans (ENNReal.ofReal_le_ofReal (hEbN (σ k))))
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  -- `H^{3/4}` bounds along the subsequence
  have hu3 : ∀ k, ∃ v3 : CubeFractionalL2 (k := 1) hd (qc)
      (qs) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
      v3.val 0 = (u (σ k) : SobolevData _).1 ∧
      cubeFractionalL2Norm hd (qc)
        (qs) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3 ≤
        Real.sqrt (max Mb 0 * Eb) := by
    intro k
    obtain ⟨v3, hv3, hb⟩ := hcoer3 (σ k) (u (σ k))
    exact ⟨v3, hv3, aux_prop_uniform_resolvent_ident_norm_bound _ _ _ Mb Eb hb (hMb k)
      (hform_nn _ _) (hEbN (σ k))⟩
  choose U3 hU3 hU3b using hu3
  -- passage on the minimizer side
  have hcu := aux_mfd_prop_as_forms_ident_functional_passage hd qc qs hr SInterp t ht (fun k => ν (σ k)) μ
    hμsupp Kμ Mbar hKμ (fun k => hνfin (σ k)) (fun k => hνsupp (σ k)) (fun k => hνmass (σ k))
    (fun k => hνgrowth (σ k)) (fun k => hνdens (σ k)) hWσ T Ktr Ctr hKtr hCtr hT
    (fun k => (u (σ k) : SobolevData _).1) (i ubar hubar)
    (by rw [hival]; exact hconv) U3 hU3 _ hU3b lam f f.continuous
  -- recovery sequence for `ustar`
  obtain ⟨v, hvb, hvconv, hvev⟩ :=
    aux_prop_uniform_resolvent_ident_recovery_reps _ a EN hEN Elim hrec ustar hustar
  obtain ⟨Es, hEs⟩ : ∃ Es : ℝ, Es = (Elim ustar).toReal + 2 := ⟨_, rfl⟩
  have hv3 : ∀ k, ∃ v3 : CubeFractionalL2 (k := 1) hd (qc)
      (qs) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
      v3.val 0 = (v (σ k) : SobolevData _).1 ∧
      cubeFractionalL2Norm hd (qc)
        (qs) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3 ≤
        Real.sqrt (max Mb 0 * Es) := by
    intro k
    obtain ⟨v3, hv3, hb⟩ := hcoer3 (σ k) (v (σ k))
    exact ⟨v3, hv3, aux_prop_uniform_resolvent_ident_norm_bound _ _ _ Mb Es hb (hMb k)
      (hform_nn _ _) (hEs ▸ hvb (σ k))⟩
  choose V3 hV3 hV3b using hv3
  have hcv := aux_mfd_prop_as_forms_ident_functional_passage hd qc qs hr SInterp t ht (fun k => ν (σ k)) μ
    hμsupp Kμ Mbar hKμ (fun k => hνfin (σ k)) (fun k => hνsupp (σ k)) (fun k => hνmass (σ k))
    (fun k => hνgrowth (σ k)) (fun k => hνdens (σ k)) hWσ T Ktr Ctr hKtr hCtr hT
    (fun k => (v (σ k) : SobolevData _).1) (i ustar hustar)
    (by rw [hival]; exact hvconv.comp hσ.tendsto_atTop) V3 hV3 _ hV3b lam f f.continuous
  -- finite-cutoff minimality along the subsequence
  have hfk : ∀ k, MemLp (f : SpatialCoordinates d → ℝ) 2 (ν (σ k)) := fun k =>
    aux_prop_uniform_resolvent_ident_memLp_of_continuous (ν (σ k)) _ hKc (hνsupp (σ k)) f
      f.continuous
  have hmink : ∀ k,
      sobolevCoefficientForm (a (σ k)) (u (σ k) : SobolevData _) (u (σ k) : SobolevData _) +
          (lam * ∫ x, ((u (σ k) : SobolevData (centeredCube (qc)
              (qs) hr)).1 x) ^ 2 ∂(ν (σ k)) -
            2 * ∫ x, f x * (u (σ k) : SobolevData (centeredCube (qc)
              (qs) hr)).1 x ∂(ν (σ k))) ≤
        sobolevCoefficientForm (a (σ k)) (v (σ k) : SobolevData _) (v (σ k) : SobolevData _) +
          (lam * ∫ x, ((v (σ k) : SobolevData (centeredCube (qc)
              (qs) hr)).1 x) ^ 2 ∂(ν (σ k)) -
            2 * ∫ x, f x * (v (σ k) : SobolevData (centeredCube (qc)
              (qs) hr)).1 x ∂(ν (σ k))) := by
    intro k
    obtain ⟨D, _, hD⟩ := hνdens (σ k)
    have := aux_prop_uniform_resolvent_ident_finite_min _ (a (σ k)) (ν (σ k)) D hD f (hfk k)
      lam hlam.le (R (σ k)) (u (σ k)) (hRu (σ k)) (hweak (σ k)) (v (σ k))
    linarith
  -- identify the limits with the functional of the parent
  have hJb2 : ∫ x, (J ubar x) ^ 2 ∂μ = ∫ x, (T (i ubar hubar) x) ^ 2 ∂μ :=
    integral_congr_ae ((hJ ubar hubar).mono fun x hx => by simp only [hx])
  have hJb1 : ∫ x, f x * J ubar x ∂μ = ∫ x, f x * T (i ubar hubar) x ∂μ :=
    integral_congr_ae ((hJ ubar hubar).mono fun x hx => by simp only [hx])
  have hJs2 : ∫ x, (J ustar x) ^ 2 ∂μ = ∫ x, (T (i ustar hustar) x) ^ 2 ∂μ :=
    integral_congr_ae ((hJ ustar hustar).mono fun x hx => by simp only [hx])
  have hJs1 : ∫ x, f x * J ustar x ∂μ = ∫ x, f x * T (i ustar hustar) x ∂μ :=
    integral_congr_ae ((hJ ustar hustar).mono fun x hx => by simp only [hx])
  obtain ⟨cT, hcT⟩ : ∃ cT : ℝ, cT = lam * ∫ x, (T (i ubar hubar) x) ^ 2 ∂μ -
    2 * ∫ x, f x * T (i ubar hubar) x ∂μ := ⟨_, rfl⟩
  obtain ⟨dT, hdT⟩ : ∃ dT : ℝ, dT = lam * ∫ x, (T (i ustar hustar) x) ^ 2 ∂μ -
    2 * ∫ x, f x * T (i ustar hustar) x ∂μ := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (Elim ubar).toReal := ⟨_, rfl⟩
  obtain ⟨Bs, hBs⟩ : ∃ Bs : ℝ, Bs = (Elim ustar).toReal := ⟨_, rfl⟩
  rw [← hcT] at hcu
  rw [← hdT] at hcv
  -- the key inequality `Func ubar ≤ Func ustar`
  have key : A + cT ≤ Bs + dT := by
    by_contra hcon
    push Not at hcon
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = A + cT - (Bs + dT) := ⟨_, rfl⟩
    have hδpos : 0 < δ := by linarith
    have e1 := (tendsto_order.1 hcu).1 (cT - δ / 4) (by linarith)
    have e2 := (tendsto_order.1 hcv).2 (dT + δ / 4) (by linarith)
    have e3 := hσ.tendsto_atTop.eventually (hvev (δ / 4) (by linarith))
    rw [← hBs] at e3
    have e4 : ∀ᶠ k in atTop,
        sobolevCoefficientForm (a (σ k)) (u (σ k) : SobolevData _) (u (σ k) : SobolevData _) <
          A - δ / 4 := by
      filter_upwards [e1, e2, e3] with k h1 h2 h3
      have := hmink k
      linarith
    obtain ⟨k0, hk0⟩ := e4.exists
    have hpos : 0 < A - δ / 4 := lt_of_le_of_lt (hform_nn _ _) hk0
    have hle : Elim ubar ≤ ENNReal.ofReal (A - δ / 4) :=
      aux_prop_uniform_resolvent_ident_liminf_subseq EN Elim hliminf σ hσ _ ubar hconv _
        (e4.mono fun k hk => (hENle (σ k) (u (σ k))).trans
          (ENNReal.ofReal_le_ofReal hk.le)).frequently
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [ENNReal.toReal_ofReal hpos.le, ← hA] at this
    linarith
  -- `ubar` is a minimizer, hence `ubar = ustar`
  refine huniq ubar hubar (fun w hw => ?_)
  have := hminle w hw
  rw [hJb2, hJb1]
  rw [hJs2, hJs1] at this
  rw [hA, hBs, hcT, hdT] at key
  linarith

theorem aux_mfd_prop_as_forms_ident_sample
    {d : ℕ} (hd : 2 ≤ d) (epsilon : ℝ) (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (qc : SpatialCoordinates d) (qs : ℝ)
    (hr : 0 < qs)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (Region : Set (SpatialCoordinates d))
    (hNeighborhood : ∀ x ∈ closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)), Metric.ball x 1 ⊆ Region)
    (muFull : Measure (SpatialCoordinates d))
    (hmu : MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) muFull ∧
      muFull (frontier ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))) = 0 ∧ muFull (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))) < ⊤)
    (Kmu : ℝ) (hKmu : 0 ≤ Kmu)
    (hgrowth : ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 →
        muFull (Metric.ball x r) ≤ ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon)) ∧
          ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon)))
    (Elim : DomainL2 (centeredCube (qc) (qs) hr) → ℝ≥0∞)
    (hmosco : _root_.SubdiffusiveProcess.ResponseMoments.MoscoLiminf (fun N u => ⨅ v : {v : killedSobolevGraph (centeredCube (qc) (qs) hr) //
          (v : SobolevData (centeredCube (qc) (qs) hr)).1 = u},
          ENNReal.ofReal (sobolevCoefficientForm
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
            (v.val : SobolevData (centeredCube (qc) (qs) hr)) (v.val : SobolevData (centeredCube (qc) (qs) hr)))) Elim ∧
      _root_.SubdiffusiveProcess.ResponseMoments.MoscoRecovery (fun N u => ⨅ v : {v : killedSobolevGraph (centeredCube (qc) (qs) hr) //
          (v : SobolevData (centeredCube (qc) (qs) hr)).1 = u},
          ENNReal.ofReal (sobolevCoefficientForm
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
            (v.val : SobolevData (centeredCube (qc) (qs) hr)) (v.val : SobolevData (centeredCube (qc) (qs) hr)))) Elim)
    (T : CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder →
      Lp ℝ 2 (muFull.restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)))))
    (Ktrace Ctrace : ℝ)
    (hT : 0 ≤ Ktrace ∧ 0 ≤ Ctrace ∧
      SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr (muFull.restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)))) Ktrace Ctrace T)
    (i : (u : DomainL2 (centeredCube (qc) (qs) hr)) → Elim u ≠ ⊤ →
      CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder)
    (hival : ∀ (u : DomainL2 (centeredCube (qc) (qs) hr)) (hu : Elim u ≠ ⊤), (i u hu).val 0 = u)
    (J : DomainL2 (centeredCube (qc) (qs) hr) → SpatialCoordinates d → ℝ)
    (hJ : ∀ (u : DomainL2 (centeredCube (qc) (qs) hr)) (hu : Elim u ≠ ⊤),
      (J u) =ᵐ[muFull.restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)))] (T (i u hu) : SpatialCoordinates d → ℝ))
    (lam : ℝ) (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (ustar : DomainL2 (centeredCube (qc) (qs) hr))
    (hmin : Elim ustar ≠ ⊤ ∧
      (∀ w : DomainL2 (centeredCube (qc) (qs) hr), Elim w ≠ ⊤ →
        (Elim ustar).toReal + lam * (∫ x, (J ustar x) ^ 2 ∂(muFull.restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))))) -
            2 * (∫ x, f x * J ustar x ∂(muFull.restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))))) ≤
          (Elim w).toReal + lam * (∫ x, (J w x) ^ 2 ∂(muFull.restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))))) -
            2 * (∫ x, f x * J w x ∂(muFull.restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)))))) ∧
      (∀ w : DomainL2 (centeredCube (qc) (qs) hr), Elim w ≠ ⊤ →
        (∀ v : DomainL2 (centeredCube (qc) (qs) hr), Elim v ≠ ⊤ →
          (Elim w).toReal + lam * (∫ x, (J w x) ^ 2 ∂(muFull.restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))))) -
              2 * (∫ x, f x * J w x ∂(muFull.restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))))) ≤
            (Elim v).toReal + lam * (∫ x, (J v x) ^ 2 ∂(muFull.restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))))) -
              2 * (∫ x, f x * J v x ∂(muFull.restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)))))) →
        w = ustar))
    (u : ℕ → killedSobolevGraph (centeredCube (qc) (qs) hr)) (R : ℕ → SpatialCoordinates d → ℝ)
    (hfinite : ∀ N : ℕ,
      (R N =ᵐ[volume.restrict ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))] ((u N : SobolevData (centeredCube (qc) (qs) hr)).1 : SpatialCoordinates d → ℝ)) ∧
      (∀ w : killedSobolevGraph (centeredCube (qc) (qs) hr),
        sobolevCoefficientForm
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
            (u N : SobolevData (centeredCube (qc) (qs) hr)) (w : SobolevData (centeredCube (qc) (qs) hr)) =
          ∫ x, (f x - lam * R N x) * (w : SobolevData (centeredCube (qc) (qs) hr)).1 x
            ∂((cutoffSpeedMeasure M H omega N).restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))))) ∧
      sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
          (u N : SobolevData (centeredCube (qc) (qs) hr)) (u N : SobolevData (centeredCube (qc) (qs) hr)) ≤
        ‖f‖ ^ 2 * ((cutoffSpeedMeasure M H omega N).restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))) ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))).toReal / lam)
    (Kc : ℕ → ℝ)
    (hcoer3 : ∀ N (v : killedSobolevGraph (centeredCube (qc) (qs) hr)),
      ∃ v3 : CubeFractionalL2 (k := 1) hd (qc)
          (qs) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
        v3.val 0 = (v : SobolevData (centeredCube (qc) (qs) hr)).1 ∧
        (cubeFractionalL2Norm hd (qc)
          (qs) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
          Kc N * sobolevCoefficientForm
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
            (v : SobolevData (centeredCube (qc) (qs) hr)) (v : SobolevData (centeredCube (qc) (qs) hr)))
    (SInterp : CubeFractionalInterpolationInput d hd)
    (g : C(SpatialCoordinates d, ℝ)) (Mb : ℝ) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hbd : ∀ k, Kc (σ k) ≤ Mb)
    (hunif : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      ∀ x ∈ closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)), |R (σ k) x - g x| < eps) :
    (g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))] (ustar : SpatialCoordinates d → ℝ) := by
  have hKc : IsCompact (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))) :=
    (centeredCube_isBounded (qc) hr).isCompact_closure
  have hlt1 : epsilon < 1 := by
    refine hepsilon'.trans ?_
    rw [div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have ht : (d : ℝ) - 1 < (d : ℝ) - epsilon := by linarith
  have hReg : ∀ x ∈ closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)), x ∈ Region := fun x hx =>
    hNeighborhood x hx (Metric.mem_ball_self one_pos)
  have hcth_cut : ∀ N, cutoffSpeedMeasure M H omega N
      (Metric.cthickening (1 / 2) (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)))) < ⊤ := fun N =>
    aux_prop_uniform_resolvent_ident_cthickening_finite _ hr Region hNeighborhood _
      (fun x hx => ((hgrowth x hx 1 one_pos le_rfl).2 N).trans_lt ENNReal.ofReal_lt_top)
  have hcth_full : muFull (Metric.cthickening (1 / 2) (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)))) < ⊤ :=
    aux_prop_uniform_resolvent_ident_cthickening_finite _ hr Region hNeighborhood _
      (fun x hx => ((hgrowth x hx 1 one_pos le_rfl).1).trans_lt ENNReal.ofReal_lt_top)
  have hW : ∀ h : SpatialCoordinates d → ℝ, Continuous h →
      Tendsto (fun N => ∫ x, h x ∂((cutoffSpeedMeasure M H omega N).restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)))))
        atTop (𝓝 (∫ x, h x ∂(muFull.restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)))))) := fun h hh =>
    aux_prop_uniform_resolvent_ident_restrict_tendsto (fun N => cutoffSpeedMeasure M H omega N)
      muFull ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)) (centeredCube _ _ hr).isOpen hKc
      (aux_prop_uniform_resolvent_ident_cube_nonempty _ hr)
      (aux_prop_uniform_resolvent_ident_cube_compl_nonempty hd _ hr) (1 / 2) (by norm_num)
      hcth_cut hcth_full hmu.1 hmu.2.1 h hh
  have : IsFiniteMeasure (muFull.restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hmu.2.2⟩
  have hsupp : ∀ ν : Measure (SpatialCoordinates d), (ν.restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)))) (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)))ᶜ = 0 := by
    intro ν
    rw [Measure.restrict_apply isClosed_closure.isOpen_compl.measurableSet, compl_inter_self,
      measure_empty]
  have hνfin : ∀ N, (cutoffSpeedMeasure M H omega N).restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))) univ < ⊤ := by
    intro N
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (Metric.self_subset_cthickening _)).trans_lt (hcth_cut N)
  obtain ⟨Mbar, hMbar⟩ := aux_prop_uniform_resolvent_ident_mass_bound
    (fun N => (cutoffSpeedMeasure M H omega N).restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))))
    (muFull.restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)))) hW (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))) hνfin
  have hνgrowth : ∀ N, ∀ x ∈ closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
      (cutoffSpeedMeasure M H omega N).restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))) (Metric.ball x rr) ≤
        ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)) := fun N x hx rr hrr hrr1 =>
    (Measure.restrict_apply_le _ _).trans ((hgrowth x (hReg x hx) rr hrr hrr1).2 N)
  have hg2 : MemLp (g : SpatialCoordinates d → ℝ) 2 (volume.restrict ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))) := by
    refine aux_prop_uniform_resolvent_ident_memLp_of_continuous _ (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))) hKc ?_ g
      g.continuous
    rw [Measure.restrict_apply isClosed_closure.isOpen_compl.measurableSet]
    exact measure_mono_null (fun x hx => hx.1 (subset_closure hx.2)) measure_empty
  have hconv : Tendsto (fun k => (u (σ k) : SobolevData (centeredCube (qc) (qs) hr)).1) atTop (𝓝 (hg2.toLp g)) :=
    aux_prop_uniform_resolvent_ident_L2_of_uniform _ hr (fun k => (u (σ k) : SobolevData (centeredCube (qc) (qs) hr)).1)
      (fun k => R (σ k)) g hg2 (fun k => (hfinite (σ k)).1) (fun ε hε => by
        obtain ⟨k0, hk0⟩ := hunif ε hε
        exact ⟨k0, fun k hk x hx => hk0 k hk x (subset_closure hx)⟩)
  have heq := aux_mfd_prop_as_forms_ident_deterministic hd qc qs hr SInterp
    ((d : ℝ) - epsilon) ht
    (fun N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
    _ (fun N u => rfl) Elim hmosco.1 hmosco.2
    (fun N => (cutoffSpeedMeasure M H omega N).restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d))))
    (muFull.restrict (closure ((centeredCube (qc) (qs) hr) : Set (SpatialCoordinates d)))) (hsupp muFull) Kmu Mbar hKmu hνfin
    (fun N => hsupp _) hMbar hνgrowth
    (fun N => aux_prop_uniform_resolvent_ident_density_le M H omega N _ hr) hW
    T Ktrace Ctrace hT.1 hT.2.1 hT.2.2 i hival J hJ lam hlam f ustar hmin u R
    (fun N => (hfinite N).1) (fun N => (hfinite N).2.1) (fun N => (hfinite N).2.2) Kc hcoer3
    σ hσ Mb hbd (hg2.toLp g) hconv
  rw [← heq]
  exact (MemLp.coeFn_toLp hg2).symm


theorem aux_mfd_prop_as_forms_Ktr_T_zero {d : ℕ} (hd : 2 ≤ d)
    {qc : SpatialCoordinates d} {qs : ℝ} {hr : 0 < qs}
    {mu : Measure (SpatialCoordinates d)} {K C : ℝ}
    {T : CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder → Lp ℝ 2 mu}
    (hT : SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr mu K C T)
    (w0 : CubeFractionalL2 (k := 1) hd (qc)
      (qs) hr halfFractionalOrder) :
    ∃ z0 : CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder,
      z0.val 0 = w0.val 0 - w0.val 0 ∧ T z0 = 0 := by
  refine ⟨⟨fun i => w0.val i - w0.val i,
    cubeFractionalL2Seminorm_sub_lt_top hd (qc)
      (qs) hr halfFractionalOrder w0.val w0.val
      w0.property w0.property⟩, rfl, ?_⟩
  have hae0 : ((⟨fun i => w0.val i - w0.val i,
      cubeFractionalL2Seminorm_sub_lt_top hd (qc)
        (qs) hr halfFractionalOrder w0.val w0.val
        w0.property w0.property⟩ : CubeFractionalL2 (k := 1) hd (qc)
          (qs) hr halfFractionalOrder).val 0 :
      SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube
        (qc) (qs) hr :
        Set (SpatialCoordinates d))] (fun _ => (0 : ℝ)) := by
    show ((w0.val 0 - w0.val 0 : DomainL2 (centeredCube (qc)
        (qs) hr)) : SpatialCoordinates d → ℝ) =ᵐ[_]
        (fun _ => (0 : ℝ))
    rw [sub_self]
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (centeredCube
      (qc) (qs) hr :
      Set (SpatialCoordinates d)))] with x hx
    simpa using hx
  have hmemlp0 : MemLp (fun _ : SpatialCoordinates d => (0 : ℝ)) 2 mu := MemLp.zero'
  rw [hT.2.2 (fun _ => (0 : ℝ)) contDiff_const _ hae0 hmemlp0]
  exact hmemlp0.toLp_zero

theorem aux_mfd_prop_as_forms_Ktr_constants
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Interp : CubeFractionalInterpolationInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHI : InfraredCharacterization M H)
    (qc : SpatialCoordinates d) (qs : ℝ) (hr : 0 < qs)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (qc)
        (qs) hr),
      ‖(v : SobolevData (centeredCube (qc)
          (qs) hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube
          (qc) (qs) hr)) v‖)
    (omega : BilateralField d)
    (G : DomainL2 (centeredCube (qc)
        (qs) hr) →L[ℝ]
      DomainL2 (centeredCube (qc)
        (qs) hr))
    (hG : ∀ f : DomainL2 (centeredCube (qc)
        (qs) hr),
      Tendsto (fun N : ℕ =>
        (responseSolution (killedResponseSpace (Ω := centeredCube
              (qc) (qs) hr) hP)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
            ((sobolevVolumeLoad f).comp
              (killedResponseSpace (Ω := centeredCube (qc)
                (qs) hr) hP).space.subtypeL)).val.1)
        atTop (𝓝 (G f)))
    (K1 : ℝ) (hK1 : 0 < K1)
    (hc1 : ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube (qc)
        (qs) hr)),
      cubeFractionalSqNorm hd (qc)
          (qs) hr threeQuarterOrder
          (v : SobolevData (centeredCube (qc)
            (qs) hr)).1 ≤
        K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
            (qc) hr)
          (v : SobolevData (centeredCube (qc)
            (qs) hr))
          (v : SobolevData (centeredCube (qc)
            (qs) hr))) :
    ∃ Ccoer Cbase Cint : ℝ, 0 < Ccoer ∧ 0 < Cbase ∧ 0 < Cint ∧
      (∀ u : DomainL2 (centeredCube (qc)
            (qs) hr),
        (limitFormEnergy G u).toENNReal ≠ ⊤ →
        ENNReal.ofReal (‖u‖ ^ 2) ≤ ENNReal.ofReal Ccoer * (limitFormEnergy G u).toENNReal) ∧
      (∀ u : DomainL2 (centeredCube (qc)
            (qs) hr),
        (limitFormEnergy G u).toENNReal ≠ ⊤ →
        ∃ v3 : CubeFractionalL2 (k := 1) hd (qc)
            (qs) hr threeQuarterOrder,
          v3.val 0 = u ∧
          (cubeFractionalL2Norm hd (qc)
            (qs) hr threeQuarterOrder v3) ^ 2 ≤
            Cbase * (limitFormEnergy G u).toReal) ∧
      (∀ (wHalf : CubeFractionalL2 (k := 1) hd (qc)
            (qs) hr halfFractionalOrder)
          (wThree : CubeFractionalL2 (k := 1) hd (qc)
            (qs) hr threeQuarterOrder),
        wThree.val 0 = wHalf.val 0 →
        cubeFractionalL2Norm hd (qc)
            (qs) hr halfFractionalOrder wHalf ≤
          Cint * (‖wHalf.val 0‖ / Real.sqrt (volume.real (centeredCube
              (qc) (qs) hr :
              Set (SpatialCoordinates d)))) ^ (1 / 3 : ℝ) *
            cubeFractionalL2Norm hd (qc)
              (qs) hr threeQuarterOrder wThree ^ (2 / 3 : ℝ)) := by
  obtain ⟨hsym, hpos, _, _⟩ := aux_car_variational_mosco (qc)
    (qs) hr hP
    (fun N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
    G hG
  obtain ⟨Ccoer, hCcoer, hcoer⟩ := aux_car_variational_limit_coercive hd Sf M H hHI omega
    (qc) (qs) hr hP K1 hK1 hc1 G
    (fun N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
    (fun _ => rfl) hsym hpos hG
  obtain ⟨Cbase, hCbase, hfrac⟩ := aux_car_variational_frac_bound hd Sf M H omega
    (qc) (qs) hr hP K1 hK1 hc1 G
    (fun N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
    (fun _ => rfl) hsym hpos hG
  obtain ⟨Cint, hCint, hinterp⟩ := Interp.interpolation_half (qc)
    (qs) hr ⟨3 / 4, by norm_num, by norm_num⟩ rfl
  exact ⟨Ccoer, Cbase, Cint, hCcoer, hCbase, hCint, hcoer, hfrac, hinterp⟩

theorem aux_mfd_prop_as_forms_Ktr_per_u
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (qc : SpatialCoordinates d) (qs : ℝ)
    (hr : 0 < qs)
    (G : DomainL2 (centeredCube (qc)
        (qs) hr) →L[ℝ]
      DomainL2 (centeredCube (qc)
        (qs) hr))
    (Ccoer Cbase Cint : ℝ) (hCcoer : 0 < Ccoer) (hCbase : 0 < Cbase) (hCint : 0 < Cint)
    (u : DomainL2 (centeredCube (qc)
        (qs) hr))
    (hu : (limitFormEnergy G u).toENNReal ≠ ⊤)
    (hcoer : ENNReal.ofReal (‖u‖ ^ 2) ≤ ENNReal.ofReal Ccoer * (limitFormEnergy G u).toENNReal)
    (hfrac : ∃ v3 : CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr threeQuarterOrder,
      v3.val 0 = u ∧ (cubeFractionalL2Norm hd (qc)
        (qs) hr threeQuarterOrder v3) ^ 2 ≤
          Cbase * (limitFormEnergy G u).toReal)
    (hinterp : ∀ (wHalf : CubeFractionalL2 (k := 1) hd (qc)
          (qs) hr halfFractionalOrder)
        (wThree : CubeFractionalL2 (k := 1) hd (qc)
          (qs) hr threeQuarterOrder),
      wThree.val 0 = wHalf.val 0 →
        cubeFractionalL2Norm hd (qc)
            (qs) hr halfFractionalOrder wHalf ≤
          Cint * (‖wHalf.val 0‖ / Real.sqrt (volume.real (centeredCube
              (qc) (qs) hr :
              Set (SpatialCoordinates d)))) ^ (1 / 3 : ℝ) *
            cubeFractionalL2Norm hd (qc)
              (qs) hr threeQuarterOrder wThree ^ (2 / 3 : ℝ))
    (i : (u' : DomainL2 (centeredCube (qc)
          (qs) hr)) →
        (limitFormEnergy G u').toENNReal ≠ ⊤ →
        CubeFractionalL2 (k := 1) hd (qc)
          (qs) hr halfFractionalOrder)
    (hi : (i u hu).val 0 = u)
    (mu : Measure (SpatialCoordinates d)) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder → Lp ℝ 2 mu)
    (hT : SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr mu K C T) (hKnn : 0 ≤ K) (hCnn : 0 ≤ C)
    (J : DomainL2 (centeredCube (qc)
        (qs) hr) → SpatialCoordinates d → ℝ)
    (hJ : (J u) =ᵐ[mu] (T (i u hu) : SpatialCoordinates d → ℝ)) :
    (∫⁻ x, ENNReal.ofReal (J u x ^ 2) ∂mu) ≤
      ENNReal.ofReal (C * (K + (mu (closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))))).toReal) *
        (Cint ^ 2 * (Ccoer / volume.real (centeredCube (qc)
            (qs) hr : Set (SpatialCoordinates d))) ^ (1/3:ℝ) *
          Cbase ^ (2/3:ℝ))) * (limitFormEnergy G u).toENNReal := by
  have hvol : 0 < volume.real (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d)) :=
    SubdiffusiveProcess.centeredCube_volume_pos (qc) hr
  obtain ⟨v3, hv3_eq, hv3_bound⟩ := hfrac
  set E := (limitFormEnergy G u).toReal with hEdef
  have hEnn : 0 ≤ E := EReal.toReal_nonneg (limitFormEnergy_nonneg G u)
  have hunorm : ‖u‖ ^ 2 ≤ Ccoer * E := by
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu) hcoer
    rwa [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hCcoer.le, EReal.toReal_toENNReal (limitFormEnergy_nonneg G u)] at h2
  have hv3norm : (cubeFractionalL2Norm hd (qc)
      (qs) hr threeQuarterOrder v3) ^ 2 ≤ Cbase * E := hv3_bound
  have hcombine := hinterp (i u hu) v3 (hv3_eq.trans hi.symm)
  rw [hi] at hcombine
  set A := ‖u‖ / Real.sqrt (volume.real (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d))) with hAdef
  set B := cubeFractionalL2Norm hd (qc)
    (qs) hr threeQuarterOrder v3 with hBdef
  have hAnn : 0 ≤ A := by rw [hAdef]; positivity
  have hBnn : 0 ≤ B := by rw [hBdef]; unfold cubeFractionalL2Norm; positivity
  have hA2 : A ^ 2 ≤ (Ccoer / volume.real (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d))) * E := by
    rw [hAdef, div_pow, Real.sq_sqrt hvol.le, div_le_iff₀ hvol, mul_right_comm,
      div_mul_cancel₀ Ccoer hvol.ne']
    exact hunorm
  have hB2 : B ^ 2 ≤ Cbase * E := hv3norm
  have hhalf_nonneg : (0:ℝ) ≤ cubeFractionalL2Norm hd (qc)
      (qs) hr halfFractionalOrder (i u hu) :=
    by unfold cubeFractionalL2Norm; positivity
  have hsq' : (cubeFractionalL2Norm hd (qc)
      (qs) hr halfFractionalOrder (i u hu)) ^ 2 ≤
      Cint ^ 2 * (Ccoer / volume.real (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d))) ^ (1/3:ℝ) *
        Cbase ^ (2/3:ℝ) * E :=
    aux_car_variational_Ktr_real_combine hvol hCcoer.le hCbase hEnn hAnn hBnn hhalf_nonneg hA2 hB2
      hcombine
  obtain ⟨z0, hz0val, hz0T⟩ := aux_mfd_prop_as_forms_Ktr_T_zero hd hT (i u hu)
  have hTlip := hT.2.1 (i u hu) z0 (i u hu) (by rw [hz0val]; abel)
  rw [hz0T, sub_zero] at hTlip
  have hnormsq : ‖T (i u hu)‖ ^ 2 ≤
      C * (K + (mu (closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))))).toReal) *
        (Cint ^ 2 * (Ccoer / volume.real (centeredCube (qc)
            (qs) hr : Set (SpatialCoordinates d))) ^ (1/3:ℝ) *
          Cbase ^ (2/3:ℝ) * E) := by
    refine hTlip.trans ?_
    apply mul_le_mul_of_nonneg_left hsq'
    have hKterm : 0 ≤ K + (mu (closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))))).toReal :=
      add_nonneg hKnn ENNReal.toReal_nonneg
    positivity
  have hlintJ : (∫⁻ x, ENNReal.ofReal (J u x ^ 2) ∂mu) =
      ∫⁻ x, ENNReal.ofReal ((T (i u hu) x) ^ 2) ∂mu := by
    apply lintegral_congr_ae
    filter_upwards [hJ] with x hx
    rw [hx]
  rw [hlintJ, aux_car_variational_Ktr_lintegral_sq_eq_norm_sq]
  have hEeq : (limitFormEnergy G u).toENNReal = ENNReal.ofReal E := by
    rw [hEdef, ← EReal.toReal_toENNReal (limitFormEnergy_nonneg G u), ENNReal.ofReal_toReal hu]
  rw [hEeq, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [hnormsq])

theorem aux_mfd_prop_as_forms_Ktr_bound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Interp : CubeFractionalInterpolationInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHI : InfraredCharacterization M H)
    (qc : SpatialCoordinates d) (qs : ℝ) (hr : 0 < qs)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (qc)
        (qs) hr),
      ‖(v : SobolevData (centeredCube (qc)
          (qs) hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube
          (qc) (qs) hr)) v‖)
    (G : BilateralField d → DomainL2 (centeredCube (qc)
        (qs) hr) →L[ℝ]
      DomainL2 (centeredCube (qc)
        (qs) hr))
    (hG_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ f : DomainL2 (centeredCube (qc)
          (qs) hr),
        Tendsto (fun N : ℕ =>
          (responseSolution (killedResponseSpace (Ω := centeredCube
                (qc) (qs) hr) hP)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
              ((sobolevVolumeLoad f).comp
                (killedResponseSpace (Ω := centeredCube (qc)
                  (qs) hr) hP).space.subtypeL)).val.1)
          atTop (𝓝 (G omega f)))
    (hK1_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K1 : ℝ, 0 < K1 ∧
      ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube (qc)
          (qs) hr)),
        cubeFractionalSqNorm hd (qc)
            (qs) hr threeQuarterOrder
            (v : SobolevData (centeredCube (qc)
              (qs) hr)).1 ≤
          K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
              (qc) hr)
            (v : SobolevData (centeredCube (qc)
              (qs) hr))
            (v : SobolevData (centeredCube (qc)
              (qs) hr)))
    (muFull : BilateralField d → Measure (SpatialCoordinates d))
    (K C : BilateralField d → ℝ)
    (T : (omega : BilateralField d) → CubeFractionalL2 (k := 1) hd
        (qc) (qs) hr
        halfFractionalOrder →
      Lp ℝ 2 ((muFull omega).restrict (closure (centeredCube
        (qc) (qs) hr :
        Set (SpatialCoordinates d)))))
    (hKC_nonneg_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, 0 ≤ K omega ∧ 0 ≤ C omega)
    (hT_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr
        ((muFull omega).restrict (closure (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))))
        (K omega) (C omega) (T omega))
    (i : (omega : BilateralField d) →
        (u : DomainL2 (centeredCube (qc)
              (qs) hr)) →
          (limitFormEnergy (G omega) u).toENNReal ≠ ⊤ →
          CubeFractionalL2 (k := 1) hd (qc)
            (qs) hr halfFractionalOrder)
    (hi_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (u : DomainL2 (centeredCube (qc)
            (qs) hr))
        (hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤), (i omega u hu).val 0 = u)
    (J : (omega : BilateralField d) → DomainL2 (centeredCube (qc)
        (qs) hr) → SpatialCoordinates d → ℝ)
    (hJ_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (u : DomainL2 (centeredCube (qc)
            (qs) hr))
        (hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤),
        (J omega u) =ᵐ[(muFull omega).restrict (closure (centeredCube
            (qc) (qs) hr :
            Set (SpatialCoordinates d)))] (T omega (i omega u hu) : SpatialCoordinates d → ℝ)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ Ktr : ℝ, 0 ≤ Ktr ∧
      ∀ (u : DomainL2 (centeredCube (qc)
            (qs) hr))
        (_hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤),
        (∫⁻ x, ENNReal.ofReal (J omega u x ^ 2)
            ∂((muFull omega).restrict (closure (centeredCube (qc)
              (qs) hr : Set (SpatialCoordinates d))))) ≤
          ENNReal.ofReal Ktr * (limitFormEnergy (G omega) u).toENNReal := by
  filter_upwards [hG_ae, hK1_ae, hKC_nonneg_ae, hT_ae, hi_ae, hJ_ae]
    with omega hG hK1all hKCnn hT hi hJ
  obtain ⟨K1, hK1, hc1⟩ := hK1all
  obtain ⟨hKnn, hCnn⟩ := hKCnn
  obtain ⟨Ccoer, Cbase, Cint, hCcoer, hCbase, hCint, hcoer, hfrac, hinterp⟩ :=
    aux_mfd_prop_as_forms_Ktr_constants hd Sf Interp M H hHI qc qs hr hP omega (G omega) hG K1 hK1
      hc1
  refine ⟨C omega * (K omega + ((muFull omega).restrict (closure (centeredCube
      (qc) (qs) hr :
      Set (SpatialCoordinates d))) (closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))))).toReal) *
      (Cint ^ 2 * (Ccoer / volume.real (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))) ^ (1/3:ℝ) *
        Cbase ^ (2/3:ℝ)), by positivity, fun u hu => ?_⟩
  exact aux_mfd_prop_as_forms_Ktr_per_u hd qc qs hr (G omega) Ccoer Cbase Cint hCcoer hCbase hCint u
    hu (hcoer u hu) (hfrac u hu) hinterp (i omega) (hi u hu)
    ((muFull omega).restrict (closure (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d))))
    (K omega) (C omega) (T omega) hT hKnn hCnn (J omega) (hJ u hu)

theorem aux_mfd_prop_as_forms_variational_step
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHI : InfraredCharacterization M H)
    (omega : BilateralField d)
    (qc : SpatialCoordinates d) (qs : ℝ) (hr : 0 < qs)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (qc)
        (qs) hr),
      ‖(v : SobolevData (centeredCube (qc)
          (qs) hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube
          (qc) (qs) hr)) v‖)
    (G : DomainL2 (centeredCube (qc)
        (qs) hr) →L[ℝ]
      DomainL2 (centeredCube (qc)
        (qs) hr))
    (hG : ∀ f : DomainL2 (centeredCube (qc)
        (qs) hr),
      Tendsto (fun N : ℕ =>
        (responseSolution (killedResponseSpace (Ω := centeredCube
              (qc) (qs) hr) hP)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
            ((sobolevVolumeLoad f).comp
              (killedResponseSpace (Ω := centeredCube (qc)
                (qs) hr) hP).space.subtypeL)).val.1)
        atTop (𝓝 (G f)))
    (K1 : ℝ) (hK1 : 0 < K1)
    (hc1 : ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube (qc)
        (qs) hr)),
      cubeFractionalSqNorm hd (qc)
          (qs) hr threeQuarterOrder
          (v : SobolevData (centeredCube (qc)
            (qs) hr)).1 ≤
        K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
            (qc) hr)
          (v : SobolevData (centeredCube (qc)
            (qs) hr))
          (v : SobolevData (centeredCube (qc)
            (qs) hr)))
    (mu muFull : Measure (SpatialCoordinates d))
    (hmu : mu = muFull.restrict
      (closure (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d))))
    (hmufin : mu Set.univ < ⊤) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder → Lp ℝ 2 mu)
    (hT : SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr mu K C T)
    (i : (u : DomainL2 (centeredCube (qc)
          (qs) hr)) →
      (limitFormEnergy G u).toENNReal ≠ ⊤ →
      CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder)
    (hi : ∀ (u : DomainL2 (centeredCube (qc)
          (qs) hr))
      (hu : (limitFormEnergy G u).toENNReal ≠ ⊤), (i u hu).val 0 = u)
    (J : DomainL2 (centeredCube (qc)
        (qs) hr) → SpatialCoordinates d → ℝ)
    (hJ : ∀ (u : DomainL2 (centeredCube (qc)
          (qs) hr))
      (hu : (limitFormEnergy G u).toENNReal ≠ ⊤),
      (J u) =ᵐ[mu] (T (i u hu) : SpatialCoordinates d → ℝ))
    (Ktr : ℝ) (hKtr : 0 ≤ Ktr)
    (hJtr : ∀ (u : DomainL2 (centeredCube (qc)
          (qs) hr))
      (_hu : (limitFormEnergy G u).toENNReal ≠ ⊤),
      (∫⁻ x, ENNReal.ofReal (J u x ^ 2) ∂mu) ≤
        ENNReal.ofReal Ktr * (limitFormEnergy G u).toENNReal)
    (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    ∃ ustar : DomainL2 (centeredCube (qc)
        (qs) hr),
      (limitFormEnergy G ustar).toENNReal ≠ ⊤ ∧
      (∀ w : DomainL2 (centeredCube (qc)
          (qs) hr),
        (limitFormEnergy G w).toENNReal ≠ ⊤ →
        (limitFormEnergy G ustar).toENNReal.toReal + lam * (∫ x, J ustar x ^ 2 ∂mu) -
            2 * ∫ x, f x * J ustar x ∂mu ≤
          (limitFormEnergy G w).toENNReal.toReal + lam * (∫ x, J w x ^ 2 ∂mu) -
            2 * ∫ x, f x * J w x ∂mu) ∧
      (∀ w : DomainL2 (centeredCube (qc)
          (qs) hr),
        (limitFormEnergy G w).toENNReal ≠ ⊤ →
        (∀ v : DomainL2 (centeredCube (qc)
            (qs) hr),
          (limitFormEnergy G v).toENNReal ≠ ⊤ →
          (limitFormEnergy G w).toENNReal.toReal + lam * (∫ x, J w x ^ 2 ∂mu) -
              2 * ∫ x, f x * J w x ∂mu ≤
            (limitFormEnergy G v).toENNReal.toReal + lam * (∫ x, J v x ^ 2 ∂mu) -
              2 * ∫ x, f x * J v x ∂mu) →
        w = ustar) := by
  obtain ⟨hsym, hpos, _, _⟩ := aux_car_variational_mosco (qc)
    (qs) hr hP
    (fun N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
    G hG
  obtain ⟨hE0, _⟩ := aux_car_variational_energy_algebra (qc)
    (qs) hr G hsym hpos
  obtain ⟨hclosed, hpara, hscale⟩ := aux_car_variational_energy_properties
    (qc) (qs) hr G hsym hpos
  obtain ⟨Ccoer, hCcoer, hcoer_cond⟩ := aux_car_variational_limit_coercive hd Sf M H hHI omega
    (qc) (qs) hr hP K1 hK1 hc1 G
    (fun N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
    (fun _ => rfl) hsym hpos hG
  have hcoer : ∃ Ccoer : ℝ, 0 < Ccoer ∧
      ∀ w : DomainL2 (centeredCube (qc)
          (qs) hr),
        ENNReal.ofReal (‖w‖ ^ 2) ≤ ENNReal.ofReal Ccoer * (limitFormEnergy G w).toENNReal := by
    refine ⟨Ccoer, hCcoer, fun w => ?_⟩
    by_cases hw : (limitFormEnergy G w).toENNReal = ⊤
    · rw [hw, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hCcoer).ne']
      exact le_top
    · exact hcoer_cond w hw
  have hpara' : ∀ (w1 w2 : DomainL2 (centeredCube (qc)
        (qs) hr)),
      (limitFormEnergy G w1).toENNReal ≠ ⊤ → (limitFormEnergy G w2).toENNReal ≠ ⊤ →
      (limitFormEnergy G (w1 + w2)).toENNReal.toReal +
          (limitFormEnergy G (w1 - w2)).toENNReal.toReal =
        2 * (limitFormEnergy G w1).toENNReal.toReal +
          2 * (limitFormEnergy G w2).toENNReal.toReal := by
    intro w1 w2 hw1 hw2
    rw [EReal.toReal_toENNReal (limitFormEnergy_nonneg G (w1 + w2)),
      EReal.toReal_toENNReal (limitFormEnergy_nonneg G (w1 - w2)),
      EReal.toReal_toENNReal (limitFormEnergy_nonneg G w1),
      EReal.toReal_toENNReal (limitFormEnergy_nonneg G w2)]
    exact hpara w1 w2 hw1 hw2
  exact aux_mfd_prop_as_forms_parts_AB hd qc qs hr G (fun u => (limitFormEnergy G u).toENNReal)
    (fun _ => rfl) mu muFull hmu hmufin K C T hT i hi J hJ hcoer
    hE0 hclosed hpara' hscale Ktr hKtr hJtr lam hlam f


lemma aux_mfd_prop_as_forms_region {d : ℕ}
    (qc : SpatialCoordinates d) (qs : ℝ) (hr : 0 < qs) :
    Bornology.IsBounded (Metric.ball (qc) (qs / 2 + 1)) ∧
      (∀ x ∈ closure ((centeredCube (qc) (qs) hr : Set (SpatialCoordinates d))),
        Metric.ball x 1 ⊆ Metric.ball (qc) (qs / 2 + 1)) := by
  refine ⟨Metric.isBounded_ball, ?_⟩
  intro x hx y hy
  rw [Metric.mem_ball] at hy ⊢
  have hcube : (centeredCube (qc) (qs) hr : Set (SpatialCoordinates d)) = Metric.ball (qc) (qs / 2) :=
    centeredCube_coe_eq_ball _ _ hr
  rw [hcube] at hx
  have hxc : x ∈ Metric.closedBall (qc) (qs / 2) :=
    Metric.closure_ball_subset_closedBall hx
  rw [Metric.mem_closedBall] at hxc
  calc dist y (qc) ≤ dist y x + dist x (qc) := dist_triangle _ _ _
    _ < 1 + qs / 2 := by linarith
    _ = qs / 2 + 1 := by ring

theorem aux_mfd_prop_as_forms_representatives
    {d : ℕ} (hd : 2 ≤ d) (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (qc : SpatialCoordinates d) (qs : ℝ) (hr : 0 < qs)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (K : ℕ → Kernel (SpatialCoordinates d) (DiffusionPath d))
    (hK : ∀ N, IsMarkovKernel (K N))
    (law : ℕ → Kernel (SpatialCoordinates d) (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ N x, Measure.map LifetimePath.ofContinuousPath (K N x) = law N x)
    (hLD : ∀ N, SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
      (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (law N))
    (Kmu : ℝ) (Region : Set (SpatialCoordinates d))
    (hNeighborhood : ∀ x ∈ closure (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d)),
      Metric.ball x 1 ⊆ Region)
    (hgrowth : ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ N,
      cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
        ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon)))
    (K1 Cext K2 : ℝ) (hK1 : 0 ≤ K1) (hCext : 0 ≤ Cext)
    (hcf : ∀ N (v : killedSobolevGraph (centeredCube (qc)
        (qs) hr)),
      cubeFractionalSqNorm hd (qc) (qs)
        hr threeQuarterOrder v.val.1 ≤
        K1 * sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N
          (qc) hr) v.val v.val)
    (hext : ∀ v : killedSobolevGraph (centeredCube (qc)
        (qs) hr),
      globalFractionalSqNorm (3 / 4)
        (Set.indicator (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))
          (fun x => v.val.1 x)) ≤
        ENNReal.ofReal (Cext * cubeFractionalSqNorm hd (qc)
          (qs) hr threeQuarterOrder v.val.1))
    (hDir : ∀ N, aux_limiting_local_energy_DirProp (qc)
      (qs) hr
      (cutoffPositiveCoefficient M H omega N (qc) hr) K2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∃ v : SpatialCoordinates d → ℝ, Continuous v ∧
        aux_cor_as_resolvent_occupation (K N)
          (centeredCube (qc) (qs) hr)
          lam f =ᵐ[volume.restrict (centeredCube (qc)
            (qs) hr : Set (SpatialCoordinates d))] v ∧
        (∀ x y, dist x y ≤ 1 → |v x - v y| ≤ C * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) ∧
        ∀ x ∉ (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d)), v x = 0 := by
  classical
  let Q := centeredCube (qc) (qs) hr
  let aN := fun N => cutoffPositiveCoefficient M H omega N (qc) hr
  let muN := fun N => cutoffSpeedMeasure M H omega N
  let RN := fun N lam f => aux_cor_as_resolvent_occupation (K N) Q lam f
  let E := fun N (v w : killedSobolevGraph Q) => sobolevCoefficientForm (aN N) v.val w.val
  have hex : ∀ (N : ℕ) (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
      ∃ u : killedSobolevGraph Q, 0 < lam →
        ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          RN N lam f) ∧
        ∀ w : killedSobolevGraph Q, E N u w =
          ∫ x in (Q : Set (SpatialCoordinates d)), (f x - lam * RN N lam f x) * w.val.1 x ∂muN N := by
    intro N lam f
    by_cases h : 0 < lam
    · have := hK N
      obtain ⟨u, hu, hw⟩ := aux_cor_as_resolvent_weak_ident M H omega N (K N)
        (law N) (hL N) (hLD N) (qc)
        (qs) hr lam h f
      exact ⟨u, fun _ => ⟨hu, hw⟩⟩
    · exact ⟨0, fun hp => (h hp).elim⟩
  choose uN huN using hex
  let uN0 := fun N lam f => (Q : Set (SpatialCoordinates d)).indicator (fun x => (uN N lam f).val.1 x)
  have hmeas : ∀ N lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      AEMeasurable (RN N lam f) ((muN N).restrict (Q : Set (SpatialCoordinates d))) := by
    intro N lam _ f
    have := hK N
    exact (aux_cor_as_resolvent_occupation_measurable (K N) Q Q.isOpen lam f).aemeasurable
  have hsource : ∀ N lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ᵐ x ∂((muN N).restrict (Q : Set (SpatialCoordinates d))), |f x - lam * RN N lam f x| ≤ 2 * ‖f‖ := by
    intro N lam hlam f
    have := hK N
    exact Eventually.of_forall (aux_cor_as_resolvent_occupation_source (K N) Q lam hlam f)
  have hcoer := fun N => aux_torsion_bound_hcoer hd (qc)
    (qs) hr (aN N) K1 Cext hK1 hCext hext (hcf N)
  have hhol := fun N => aux_torsion_bound_hHol (qc)
    (qs) hr (aN N) K2 (hDir N)
  have hac : ∀ N, (muN N).restrict (Q : Set (SpatialCoordinates d)) ≪ volume := by
    intro N
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans
      (withDensity_absolutelyContinuous _ _)
  obtain ⟨A, hA, hosc⟩ := aux_mfd_prop_as_forms_osc_omega hd epsilon
    hepsilon hepsilon' qc qs hr muN E RN uN uN0 aN (fun _ _ _ => rfl)
    hmeas hsource Kmu (fun _ => K1 * ((qs) ^ d + Cext))
    (fun _ => K2 * Real.sqrt (d : ℝ) ^ (1 / 2 : ℝ))
    (by constructor <;> exact ⟨_, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩) Region hNeighborhood
    (fun N lam hlam f => (huN N lam f hlam).2) (fun _ _ _ _ => rfl) hgrowth hcoer hhol hac
  obtain ⟨Cc, hCc, hcamp⟩ := aux_cor_as_resolvent_hcamp_final Cp (1 / 4) ⟨by norm_num, by norm_num⟩
  refine ⟨Cc * A, mul_nonneg hCc.le hA, ?_⟩
  intro N lam hlam f
  have hbeta : (1 / 4 : ℝ) ≤ 1 / 2 - ((d : ℝ) + 2) * epsilon :=
    (aux_prop_uniform_resolvent_cutoff_oscillation_exponent hd epsilon hepsilon hepsilon').le
  obtain ⟨v, hvc, hvae, hvhol, hv0⟩ := aux_prop_uniform_resolvent_camp_holder
    (qc) (qs) hr Cc hcamp
    (1 / 2 - ((d : ℝ) + 2) * epsilon) hbeta (A * ‖f‖)
    (mul_nonneg hA (norm_nonneg f)) (uN N lam f).val.1 (hosc N lam hlam f)
  refine ⟨v, hvc, ?_, ?_, hv0⟩
  · have hrep : (uN N lam f).val.1 =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] v := by
      filter_upwards [ae_restrict_of_ae hvae, ae_restrict_mem Q.isOpen.measurableSet] with x hx hxQ
      change v x = (Q : Set (SpatialCoordinates d)).indicator (fun y => (uN N lam f).val.1 y) x at hx
      rw [Set.indicator_of_mem hxQ] at hx
      exact hx.symm
    exact (huN N lam f hlam).1.symm.trans hrep
  · intro x y hxy
    simpa only [mul_assoc] using hvhol x y hxy

theorem aux_mfd_prop_as_forms_holder_supply
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Interp : CubeFractionalInterpolationInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M)
        (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg), M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ N, IsMarkovKernel (KN N)) → in_crossing M H PN KN →
        aux_cutoff_lifetime_package_LocalInput M H KN →
      ∀ (qc : ℕ → SpatialCoordinates d) (qs : ℕ → ℝ)
        (hr : ∀ n : ℕ, 0 < qs n)
        (_htri : ∀ n : ℕ, ∃ j : ℤ, qs n = (3 : ℝ) ^ j)
        (RN : ℕ → ℕ → BilateralField d → ℝ →
            BoundedContinuousFunction (SpatialCoordinates d) ℝ →
            SpatialCoordinates d → ℝ)
        (_hRN_formula : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
            (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
            (x : SpatialCoordinates d),
          RN n N omega lam f x =
            ∫ path, (∫ t in Set.Ioi (0 : ℝ),
              Set.indicator
                {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                  (centeredCube (qc n)
                    (qs n) (hr n) : Set (SpatialCoordinates d)) path}
                (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
              ∂(KN N (omega, x)))
        (n0 : ℕ),
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        (∃ K1 : ℝ, 0 < K1 ∧ ∀ (N : ℕ)
          (v : killedSobolevGraph (centeredCube (qc n0) (qs n0) (hr n0))),
          cubeFractionalSqNorm hd (qc n0) (qs n0) (hr n0) threeQuarterOrder v.val.1 ≤
            K1 * sobolevCoefficientForm
              (cutoffPositiveCoefficient M H omega N (qc n0) (hr n0)) v.val v.val) ∧
        ∀ (lam0 lam1 : ℝ), 0 < lam0 → lam0 ≤ lam1 →
          ∃ Kom : ℝ, 0 < Kom ∧ ∀ (N : ℕ) (lam : ℝ), lam0 ≤ lam → lam ≤ lam1 →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ‖f‖ ≤ 1 →
              (∀ x ∈ closure (centeredCube (qc n0)
                  (qs n0) (hr n0) : Set (SpatialCoordinates d)),
                |RN n0 N omega lam f x| ≤ Kom) ∧
              ∀ x ∈ closure (centeredCube (qc n0)
                  (qs n0) (hr n0) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure (centeredCube (qc n0)
                  (qs n0) (hr n0) : Set (SpatialCoordinates d)),
                |RN n0 N omega lam f x - RN n0 N omega lam f y| ≤
                  Kom * dist x y ^ (1 / 4 : ℝ)  := by


  classical
  let epsilon : ℝ := 1 / (16 * ((d : ℝ) + 2))
  have heps := aux_cor_as_resolvent_cube_cutoff_holder_eps_choice hd
  have heps1 : epsilon < 1 := by
    dsimp only [epsilon]
    apply (div_lt_one (by positivity)).2
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨δg, hδg, hgrowth⟩ := prop_chaos_growth hd epsilon ⟨heps.1, heps1⟩
    (16 * d * (d + 2) + 1) (aux_cor_as_resolvent_cube_cutoff_holder_p_choice hd)
  obtain ⟨δc, hδc, hcoarse⟩ := lem_as_coarse d hd Jc Pc Xc Sf W Cp D aux_lem_band_rcJ_hES Step Dbase Interp 1 (3 / 4)
    ⟨one_pos, le_rfl⟩ ⟨by norm_num, by norm_num⟩
  obtain ⟨δr, hδr, hregular⟩ := lem_as_regularity d hd Jc Pc Xc W D Cp Sf Step Dbase Interp
    (1 / 2) (3 / 4) ((d : ℝ) - 3 / 4) ((d : ℝ) - 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
  refine ⟨min δg (min 1 (min δc δr)), lt_min hδg (lt_min one_pos (lt_min hδc hδr)), ?_⟩
  intro M Rm Sreg It hδ H HI PN KN hKN hin hinput qc qs hr htri RN hRN n0
  have hδg' : M.delta ≤ δg := hδ.trans (min_le_left _ _)
  have hδ1 : M.delta ≤ 1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδc' : M.delta ≤ δc := hδ.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδr' : M.delta ≤ δr := hδ.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let Q := centeredCube (qc n0)
    (qs n0) (hr n0)
  let Region := Metric.ball (qc n0)
    (qs n0 / 2 + 1)
  have hRegion := aux_mfd_prop_as_forms_region (qc n0) (qs n0) (hr n0)
  obtain ⟨mu, _, _, hg⟩ := hgrowth M H HI hδg'
  obtain ⟨Kmu, _, hKmu⟩ := hg Region hRegion.1
  have eC := hcoarse M Rm Sreg It H HI (le_min hδ1 hδc')
    (qc n0) (qs n0) (hr n0)
    (htri n0)
  have eR := hregular M Rm Sreg It H HI (le_min hδ1 hδr')
    (qc n0) (qs n0) (hr n0)
  obtain ⟨Cext, hCext, hext, _⟩ := killed_zero_extension_bound hd Sf
    (qc n0) (qs n0) (hr n0)
  have hac := car_resolvent_abs_cont hd M H HI PN KN hKN hin hinput
  have hpoint := aux_mfd_prop_as_forms_continuous_version hd M H HI PN KN hKN hin hinput hac qc qs hr RN hRN
  filter_upwards [eC, eR, hKmu, hinput.localDiffusion, hpoint, hin.2.2] with omega hC hR hgω hLD hpointω hfdd
  obtain ⟨K1, hK1, hcf⟩ := hC
  obtain ⟨K2, hK2, hDir⟩ := hR
  let K := fun N => (KN N).comap (fun x : SpatialCoordinates d => (omega,x))
    (measurable_const.prodMk measurable_id)
  have hK : ∀ N, IsMarkovKernel (K N) := by
    intro N
    have := hKN N
    dsimp only [K]
    infer_instance
  have hL : ∀ N x, Measure.map LifetimePath.ofContinuousPath (K N x) =
      aux_cutoff_lifetime_package_kernel KN N omega x :=
    fun N x => aux_cutoff_lifetime_package_spec KN N omega x
  have hgr : ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ N,
      cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
        ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)) := by
    intro x hx r hr0 hr1 N
    rw [cutoffSpeedMeasure_eq_weightedChaosCutoff]
    exact hgω.2.1 N x hx r hr0 hr1
  have hD : ∀ N, aux_limiting_local_energy_DirProp (qc n0)
      (qs n0) (hr n0)
      (cutoffPositiveCoefficient M H omega N (qc n0) (hr n0)) K2 := by
    intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol
    exact ((hDir N).1 F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol).2
  obtain ⟨C, hC0, hrep⟩ := aux_mfd_prop_as_forms_representatives hd Cp epsilon heps.1 heps.2
    (qc n0) (qs n0) (hr n0) M H omega K hK (fun N => aux_cutoff_lifetime_package_kernel KN N omega)
    hL hLD (Kmu omega) Region hRegion.2 hgr K1 Cext K2 hK1.le hCext.le
    (fun N v => (hcf true).2.1 N v) hext hD
  have hRN' : ∀ N lam f, RN n0 N omega lam f = aux_cor_as_resolvent_occupation (K N) Q lam f := by
    intro N lam f
    funext x
    exact hRN n0 N omega lam f x
  have hstart : ∀ N x, ∀ᵐ p ∂K N x, p 0 = x := by
    intro N x
    apply aux_cor_as_resolvent_start (PN N omega) (K N x) x
    change (KN N (omega,x)).map _ = _
    rw [← Kernel.map_apply (KN N) (ContinuousPath.measurable_finsetEvaluation
      (alpha := SpatialCoordinates d) ({0} : Finset ℝ≥0)) (omega,x)]
    exact hfdd N ({0} : Finset ℝ≥0) x
  have habs : ∀ N lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ x, |RN n0 N omega lam f x| ≤ ‖f‖ / lam := by
    intro N lam hlam f x
    have := hK N
    rw [hRN']
    exact aux_cor_as_resolvent_occupation_bound (K N) Q lam hlam f x
  have hlocal : ∀ N lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ y ∈ closure (Q : Set (SpatialCoordinates d)),
        dist x y ≤ 1 → |RN n0 N omega lam f x - RN n0 N omega lam f y| ≤
          C * ‖f‖ * dist x y ^ (1 / 4 : ℝ) := by
    intro N lam hlam f
    obtain ⟨v, hvc, hvae, hvhol, hv0⟩ := hrep N lam hlam f
    have hRv : RN n0 N omega lam f = v := by
      funext x
      by_cases hx : x ∈ (Q : Set (SpatialCoordinates d))
      · apply hpointω n0 N lam hlam f v hvc.continuousOn
        · rw [hRN']; exact hvae
        · exact hx
      · rw [hRN', aux_cor_as_resolvent_occupation_zero (K N) (hstart N) Q lam f x hx, hv0 x hx]
    intro x _ y _ hxy
    rw [hRv]
    exact hvhol x y hxy
  refine ⟨⟨K1, hK1, fun N v => (hcf true).2.1 N v⟩, ?_⟩
  intro lam0 lam1 hlam0 _
  obtain ⟨Kom, hKom, hKomall⟩ := aux_cor_as_resolvent_compact_range (Q : Set (SpatialCoordinates d))
    lam0 C hlam0 hC0 (fun N lam f => RN n0 N omega lam f) habs hlocal
  exact ⟨Kom, hKom, fun N lam hlow _ f hf => hKomall N lam hlow f hf⟩


theorem aux_mfd_prop_as_forms_RN_zero_outside
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (qc : ℕ → SpatialCoordinates d) (qs : ℕ → ℝ)
    (hr : ∀ n : ℕ, 0 < qs n)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hstart : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, ∀ x : SpatialCoordinates d,
      ∀ᵐ path ∂(KN N (omega, x)), path (0 : ℝ≥0) = x)
    (RN : ℕ → ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
        (x : SpatialCoordinates d),
      RN n N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (qc n)
                (qs n) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x))) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ x ∉ (centeredCube (qc n)
              (qs n) (hr n) : Set (SpatialCoordinates d)),
            RN n N omega lam f x = 0 := by
  filter_upwards [hstart] with omega hω
  intro n N lam hlam f x hx
  rw [hRN n N omega lam f x]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hω N x] with path hpath
  have hExit : ContinuousPath.exitTime
      (centeredCube (qc n)
        (qs n) (hr n) : Set (SpatialCoordinates d)) path = 0 := by
    apply le_antisymm _ (zero_le)
    have hle := ContinuousPath.exitTime_le_of_notMem
      (centeredCube (qc n)
        (qs n) (hr n) : Set (SpatialCoordinates d))
      path 0 (by rw [hpath]; exact hx)
    simpa using hle
  have hempty : {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
      (centeredCube (qc n)
        (qs n) (hr n) : Set (SpatialCoordinates d)) path} = ∅ := by
    ext s
    simp [hExit]
  simp [hempty]

theorem aux_mfd_prop_as_forms_RN_bound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (_M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (qc : ℕ → SpatialCoordinates d) (qs : ℕ → ℝ)
    (hr : ∀ n : ℕ, 0 < qs n)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (RN : ℕ → ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
        (x : SpatialCoordinates d),
      RN n N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (qc n)
                (qs n) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x))) :
    ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x ∈ (centeredCube (qc n)
            (qs n) (hr n) : Set (SpatialCoordinates d)),
          |RN n N omega lam f x| ≤ ‖f‖ / lam := by
  intro n N omega lam hlam f x hx
  rw [hRN n N omega lam f x]
  let : IsMarkovKernel (KN N) := hKN N
  let : IsProbabilityMeasure (KN N (omega, x)) :=
    IsMarkovKernel.isProbabilityMeasure (omega, x)
  have hpath : ∀ path : DiffusionPath d,
      |∫ t in Set.Ioi (0 : ℝ),
        Set.indicator
          {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
            (centeredCube (qc n)
              (qs n) (hr n) : Set (SpatialCoordinates d)) path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t| ≤ ‖f‖ / lam := by
    intro path
    simpa [Real.norm_eq_abs, aux_prop_uniform_resolvent_point_G,
      aux_prop_uniform_resolvent_point_F] using
      (aux_prop_uniform_resolvent_point_G_abs_le
        (centeredCube (qc n)
          (qs n) (hr n) : Set (SpatialCoordinates d))
        lam hlam (fun y => f y) ‖f‖
        (fun y => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm y) path)
  have h_ae_bound : ∀ᵐ path ∂(KN N (omega, x)),
      ‖(∫ t in Set.Ioi (0 : ℝ),
        Set.indicator
          {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
            (centeredCube (qc n)
              (qs n) (hr n) : Set (SpatialCoordinates d)) path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)‖ ≤ ‖f‖ / lam := by
    filter_upwards [] with path
    simpa [Real.norm_eq_abs] using hpath path
  have hnorm := norm_integral_le_of_norm_le_const h_ae_bound
  simpa [Real.norm_eq_abs, MeasureTheory.probReal_univ, mul_one] using hnorm

theorem aux_mfd_prop_as_forms_RN_smul
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (qc : ℕ → SpatialCoordinates d) (qs : ℕ → ℝ)
    (hr : ∀ n : ℕ, 0 < qs n)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (RN : ℕ → ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN_formula : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d),
      RN n N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (qc n)
                (qs n) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x))) :
    ∀ (n N : ℕ) (omega : BilateralField d) (c lam : ℝ)
      (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d),
      RN n N omega lam (c • f) x = c * RN n N omega lam f x := by
  intro n N omega c lam f x
  rw [hRN_formula, hRN_formula]
  set μ : Measure (DiffusionPath d) := KN N (omega, x)
  have hinner : ∀ path : DiffusionPath d,
      (∫ t in Set.Ioi (0 : ℝ), Set.indicator
          {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
            (centeredCube (qc n)
              (qs n) (hr n) : Set (SpatialCoordinates d)) path}
          (fun s : ℝ => Real.exp (-lam * s) * (c • f) (path (Real.toNNReal s))) t)
        = c * (∫ t in Set.Ioi (0 : ℝ), Set.indicator
          {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
            (centeredCube (qc n)
              (qs n) (hr n) : Set (SpatialCoordinates d)) path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) := by
    intro path
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
        (centeredCube (qc n)
          (qs n) (hr n) : Set (SpatialCoordinates d)) path}
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht,
        BoundedContinuousFunction.smul_apply, smul_eq_mul]
      ring
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
      ring
  calc
    ∫ path, (∫ t in Set.Ioi (0 : ℝ), Set.indicator
        {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
          (centeredCube (qc n)
            (qs n) (hr n) : Set (SpatialCoordinates d)) path}
        (fun s : ℝ => Real.exp (-lam * s) * (c • f) (path (Real.toNNReal s))) t) ∂μ
        = ∫ path, c * (∫ t in Set.Ioi (0 : ℝ), Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (qc n)
                (qs n) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) ∂μ := by
      apply integral_congr_ae
      filter_upwards with path
      exact hinner path
    _ = c * ∫ path, (∫ t in Set.Ioi (0 : ℝ), Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (qc n)
                (qs n) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) ∂μ := by
      rw [integral_const_mul]

theorem aux_mfd_prop_as_forms_holder_all
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (qc : ℕ → SpatialCoordinates d) (qs : ℕ → ℝ)
    (hr : ∀ n : ℕ, 0 < qs n)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (RN : ℕ → ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN_formula : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d),
      RN n N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (qc n)
                (qs n) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x)))
    (n0 : ℕ)
    (hHolder : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam0 lam1 : ℝ), 0 < lam0 → lam0 ≤ lam1 →
        ∃ Kom : ℝ, 0 < Kom ∧ ∀ (N : ℕ) (lam : ℝ), lam0 ≤ lam → lam ≤ lam1 →
          ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ‖f‖ ≤ 1 →
            (∀ x ∈ closure (centeredCube (qc n0)
                (qs n0) (hr n0) : Set (SpatialCoordinates d)),
              |RN n0 N omega lam f x| ≤ Kom) ∧
            ∀ x ∈ closure (centeredCube (qc n0)
                (qs n0) (hr n0) : Set (SpatialCoordinates d)),
            ∀ y ∈ closure (centeredCube (qc n0)
                (qs n0) (hr n0) : Set (SpatialCoordinates d)),
              |RN n0 N omega lam f x - RN n0 N omega lam f y| ≤
                Kom * dist x y ^ (1 / 4 : ℝ)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ),
            ∀ x ∈ closure (centeredCube (qc n0)
                (qs n0) (hr n0) : Set (SpatialCoordinates d)),
            ∀ y ∈ closure (centeredCube (qc n0)
                (qs n0) (hr n0) : Set (SpatialCoordinates d)),
              |RN n0 N omega lam f x - RN n0 N omega lam f y| ≤
                C * dist x y ^ (1 / 4 : ℝ) := by
  filter_upwards [hHolder] with omega hω
  intro lam hlam f
  let c : ℝ := max ‖f‖ 1
  have hc : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
  let f0 : BoundedContinuousFunction (SpatialCoordinates d) ℝ := c⁻¹ • f
  have hf0 : ‖f0‖ ≤ 1 := by
    dsimp [f0]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc]
    calc
      c⁻¹ * ‖f‖ = ‖f‖ / c := by rw [div_eq_mul_inv, mul_comm]
      _ ≤ 1 := by
        apply (div_le_iff₀ hc).2
        calc
          ‖f‖ ≤ max ‖f‖ 1 := le_max_left _ _
          _ = 1 * c := by simp [c]
  have hf_eq : c • f0 = f := by
    ext x
    dsimp [f0]
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  obtain ⟨C, hC, hCbound⟩ := hω lam lam hlam le_rfl
  refine ⟨c * C, mul_pos hc hC, ?_⟩
  intro N x hx y hy
  obtain ⟨_, hosc⟩ := hCbound N lam le_rfl le_rfl f0 hf0
  have h := hosc x hx y hy
  have hscale_x := aux_mfd_prop_as_forms_RN_smul qc qs hr KN RN hRN_formula
    n0 N omega c lam f0 x
  have hscale_y := aux_mfd_prop_as_forms_RN_smul qc qs hr KN RN hRN_formula
    n0 N omega c lam f0 y
  have hx_eq : RN n0 N omega lam f x = c * RN n0 N omega lam f0 x := by
    calc
      RN n0 N omega lam f x = RN n0 N omega lam (c • f0) x := by rw [hf_eq]
      _ = c * RN n0 N omega lam f0 x := hscale_x
  have hy_eq : RN n0 N omega lam f y = c * RN n0 N omega lam f0 y := by
    calc
      RN n0 N omega lam f y = RN n0 N omega lam (c • f0) y := by rw [hf_eq]
      _ = c * RN n0 N omega lam f0 y := hscale_y
  rw [hx_eq, hy_eq, ← mul_sub, abs_mul, abs_of_pos hc]
  exact (mul_le_mul_of_nonneg_left h hc.le).trans_eq (by ring)

theorem aux_mfd_prop_as_forms_RN_continuous
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (qc : ℕ → SpatialCoordinates d) (qs : ℕ → ℝ)
    (hr : ∀ n : ℕ, 0 < qs n)
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d}
    (RN : ℕ → ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (n0 : ℕ)
    (hHolderAll : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ),
            ∀ x ∈ closure (centeredCube (qc n0)
                (qs n0) (hr n0) : Set (SpatialCoordinates d)),
            ∀ y ∈ closure (centeredCube (qc n0)
                (qs n0) (hr n0) : Set (SpatialCoordinates d)),
              |RN n0 N omega lam f x - RN n0 N omega lam f y| ≤
                C * dist x y ^ (1 / 4 : ℝ)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ N : ℕ, ContinuousOn (fun x => RN n0 N omega lam f x)
            (closure (centeredCube (qc n0)
              (qs n0) (hr n0) : Set (SpatialCoordinates d))) := by
  filter_upwards [hHolderAll] with omega hω
  intro lam hlam f N
  obtain ⟨C, hC, hbound⟩ := hω lam hlam f
  rw [Metric.continuousOn_iff]
  intro b hb eps heps
  refine ⟨(eps / C) ^ 4, by positivity, ?_⟩
  intro a ha hdist
  have hab := hbound N a ha b hb
  rw [Real.dist_eq]
  rcases eq_or_lt_of_le (dist_nonneg : (0 : ℝ) ≤ dist a b) with hzero | hpos
  · rw [← hzero, Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), mul_zero] at hab
    linarith
  · have hlt : dist a b ^ (1 / 4 : ℝ) < eps / C := by
      have hpow : ((eps / C) ^ 4 : ℝ) ^ (1 / 4 : ℝ) = eps / C := by
        have h4 : ((eps / C) ^ 4 : ℝ) = (eps / C) ^ (4 : ℝ) := by
          norm_num [Real.rpow_natCast]
        rw [h4, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ eps / C)
          (4 : ℝ) (1 / 4), show (4 : ℝ) * (1 / 4) = 1 by norm_num,
          Real.rpow_one]
      exact (Real.rpow_lt_rpow hpos.le hdist (by norm_num)).trans_eq hpow
    have hstrict : C * dist a b ^ (1 / 4 : ℝ) < eps := by
      simpa [mul_comm] using (lt_div_iff₀ hC).mp hlt
    linarith

theorem aux_mfd_prop_as_forms_hidentify_at_omega
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (epsilon : ℝ) (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (qc : SpatialCoordinates d) (qs : ℝ)
    (hr : 0 < qs)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (Region : Set (SpatialCoordinates d))
    (hNeighborhood : ∀ x ∈ closure ((centeredCube (qc)
        (qs) hr) : Set (SpatialCoordinates d)),
      Metric.ball x 1 ⊆ Region)
    (muFull : Measure (SpatialCoordinates d))
    (hmu : MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) muFull ∧
      muFull (frontier ((centeredCube (qc)
          (qs) hr) : Set (SpatialCoordinates d))) = 0 ∧
      muFull (closure ((centeredCube (qc)
          (qs) hr) : Set (SpatialCoordinates d))) < ⊤)
    (Kmu : ℝ) (hKmu : 0 ≤ Kmu)
    (hgrowth : ∀ x ∈ Region, ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
      muFull (Metric.ball x rr) ≤ ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)) ∧
        ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x rr) ≤
          ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)))
    (Elim : DomainL2 (centeredCube (qc)
        (qs) hr) → ℝ≥0∞)
    (hmosco : _root_.SubdiffusiveProcess.ResponseMoments.MoscoLiminf (fun N u => ⨅ v : {v : killedSobolevGraph (centeredCube
          (qc) (qs) hr) //
        (v : SobolevData (centeredCube (qc)
          (qs) hr)).1 = u},
        ENNReal.ofReal (sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
          (v.val : SobolevData (centeredCube (qc)
            (qs) hr))
          (v.val : SobolevData (centeredCube (qc)
            (qs) hr)))) Elim ∧
      _root_.SubdiffusiveProcess.ResponseMoments.MoscoRecovery (fun N u => ⨅ v : {v : killedSobolevGraph (centeredCube
          (qc) (qs) hr) //
        (v : SobolevData (centeredCube (qc)
          (qs) hr)).1 = u},
        ENNReal.ofReal (sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
          (v.val : SobolevData (centeredCube (qc)
            (qs) hr))
          (v.val : SobolevData (centeredCube (qc)
            (qs) hr)))) Elim)
    (T : CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder →
      Lp ℝ 2 (muFull.restrict (closure ((centeredCube (qc)
        (qs) hr) : Set (SpatialCoordinates d)))))
    (Ktrace Ctrace : ℝ)
    (hT : 0 ≤ Ktrace ∧ 0 ≤ Ctrace ∧
      SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr (muFull.restrict (closure
        ((centeredCube (qc)
          (qs) hr) : Set (SpatialCoordinates d)))) Ktrace Ctrace T)
    (i : (u : DomainL2 (centeredCube (qc)
          (qs) hr)) → Elim u ≠ ⊤ →
      CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder)
    (hival : ∀ (u : DomainL2 (centeredCube (qc)
          (qs) hr)) (hu : Elim u ≠ ⊤), (i u hu).val 0 = u)
    (J : DomainL2 (centeredCube (qc)
        (qs) hr) → SpatialCoordinates d → ℝ)
    (hJ : ∀ (u : DomainL2 (centeredCube (qc)
          (qs) hr)) (hu : Elim u ≠ ⊤),
      (J u) =ᵐ[muFull.restrict (closure ((centeredCube (qc)
          (qs) hr) : Set (SpatialCoordinates d)))]
        (T (i u hu) : SpatialCoordinates d → ℝ))
    (lam : ℝ) (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (ustar : DomainL2 (centeredCube (qc)
        (qs) hr))
    (hmin : Elim ustar ≠ ⊤ ∧
      (∀ w : DomainL2 (centeredCube (qc)
          (qs) hr), Elim w ≠ ⊤ →
        (Elim ustar).toReal + lam * (∫ x, (J ustar x) ^ 2 ∂(muFull.restrict (closure
            ((centeredCube (qc)
              (qs) hr) : Set (SpatialCoordinates d))))) -
          2 * (∫ x, f x * J ustar x ∂(muFull.restrict (closure
            ((centeredCube (qc)
              (qs) hr) : Set (SpatialCoordinates d))))) ≤
        (Elim w).toReal + lam * (∫ x, (J w x) ^ 2 ∂(muFull.restrict (closure
            ((centeredCube (qc)
              (qs) hr) : Set (SpatialCoordinates d))))) -
          2 * (∫ x, f x * J w x ∂(muFull.restrict (closure
            ((centeredCube (qc)
              (qs) hr) : Set (SpatialCoordinates d)))))) ∧
      (∀ w : DomainL2 (centeredCube (qc)
          (qs) hr), Elim w ≠ ⊤ →
        (∀ v : DomainL2 (centeredCube (qc)
            (qs) hr), Elim v ≠ ⊤ →
          (Elim w).toReal + lam * (∫ x, (J w x) ^ 2 ∂(muFull.restrict (closure
              ((centeredCube (qc)
                (qs) hr) : Set (SpatialCoordinates d))))) -
            2 * (∫ x, f x * J w x ∂(muFull.restrict (closure
              ((centeredCube (qc)
                (qs) hr) : Set (SpatialCoordinates d))))) ≤
            (Elim v).toReal + lam * (∫ x, (J v x) ^ 2 ∂(muFull.restrict (closure
              ((centeredCube (qc)
                (qs) hr) : Set (SpatialCoordinates d))))) -
              2 * (∫ x, f x * J v x ∂(muFull.restrict (closure
              ((centeredCube (qc)
                (qs) hr) : Set (SpatialCoordinates d)))))) →
        w = ustar))
    (u : ℕ → killedSobolevGraph (centeredCube (qc)
        (qs) hr))
    (R : ℕ → SpatialCoordinates d → ℝ)
    (hfinite : ∀ N : ℕ,
      (R N =ᵐ[volume.restrict ((centeredCube (qc)
          (qs) hr) : Set (SpatialCoordinates d))]
        ((u N : SobolevData (centeredCube (qc)
          (qs) hr)).1 : SpatialCoordinates d → ℝ)) ∧
      (∀ w : killedSobolevGraph (centeredCube (qc)
          (qs) hr),
        sobolevCoefficientForm
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
            (u N : SobolevData (centeredCube (qc)
              (qs) hr))
            (w : SobolevData (centeredCube (qc)
              (qs) hr)) =
          ∫ x, (f x - lam * R N x) * (w : SobolevData (centeredCube
              (qc) (qs) hr)).1 x
            ∂((cutoffSpeedMeasure M H omega N).restrict (closure
              ((centeredCube (qc)
                (qs) hr) : Set (SpatialCoordinates d))))) ∧
      sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
          (u N : SobolevData (centeredCube (qc)
            (qs) hr))
          (u N : SobolevData (centeredCube (qc)
            (qs) hr)) ≤
        ‖f‖ ^ 2 * ((cutoffSpeedMeasure M H omega N).restrict (closure
            ((centeredCube (qc)
              (qs) hr) : Set (SpatialCoordinates d)))
          ((centeredCube (qc)
            (qs) hr) : Set (SpatialCoordinates d))).toReal / lam)
    (K1 : ℝ) (_hK1 : 0 < K1)
    (hc1 : ∀ N (v : killedSobolevGraph (centeredCube (qc)
        (qs) hr)),
      ∃ v3 : CubeFractionalL2 (k := 1) hd (qc)
          (qs) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
        v3.val 0 = (v : SobolevData (centeredCube (qc)
          (qs) hr)).1 ∧
        (cubeFractionalL2Norm hd (qc)
          (qs) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
          K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
              (qc) hr)
            (v : SobolevData (centeredCube (qc)
              (qs) hr))
            (v : SobolevData (centeredCube (qc)
              (qs) hr)))
    (SInterp : CubeFractionalInterpolationInput d hd)
    (g : C(SpatialCoordinates d, ℝ)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hunif : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      ∀ x ∈ closure ((centeredCube (qc)
        (qs) hr) : Set (SpatialCoordinates d)),
        |R (σ k) x - g x| < eps) :
    (g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict ((centeredCube
      (qc) (qs) hr) :
      Set (SpatialCoordinates d))] (ustar : SpatialCoordinates d → ℝ) :=
  aux_mfd_prop_as_forms_ident_sample hd epsilon hepsilon' qc qs hr M H omega Region
    hNeighborhood muFull hmu Kmu hKmu hgrowth Elim hmosco T Ktrace Ctrace hT i hival J hJ
    lam hlam f ustar hmin u R hfinite (fun _ => K1) hc1 SInterp g K1 σ hσ (fun _ => le_refl K1)
    hunif

theorem aux_mfd_prop_as_forms_hidentify_and_converge
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (qc : SpatialCoordinates d) (qs : ℝ) (hr : 0 < qs)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (qc)
        (qs) hr),
      ‖(v : SobolevData (centeredCube (qc)
          (qs) hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube
          (qc) (qs) hr)) v‖)
    (omega : BilateralField d)
    (G : DomainL2 (centeredCube (qc)
        (qs) hr) →L[ℝ]
      DomainL2 (centeredCube (qc)
        (qs) hr))
    (hG : ∀ f : DomainL2 (centeredCube (qc)
        (qs) hr),
      Tendsto (fun N : ℕ =>
        (responseSolution (killedResponseSpace (Ω := centeredCube
              (qc) (qs) hr) hP)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
            ((sobolevVolumeLoad f).comp
              (killedResponseSpace (Ω := centeredCube (qc)
                (qs) hr) hP).space.subtypeL)).val.1)
        atTop (𝓝 (G f)))
    (K1 : ℝ) (hK1 : 0 < K1)
    (hc1 : ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube (qc)
        (qs) hr)),
      cubeFractionalSqNorm hd (qc)
          (qs) hr threeQuarterOrder
          (v : SobolevData (centeredCube (qc)
            (qs) hr)).1 ≤
        K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
            (qc) hr)
          (v : SobolevData (centeredCube (qc)
            (qs) hr))
          (v : SobolevData (centeredCube (qc)
            (qs) hr)))
    (muFull : Measure (SpatialCoordinates d))
    (hmuFull1 : MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) muFull ∧
      muFull (frontier (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))) = 0 ∧
      muFull (closure (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))) < ⊤)
    (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder →
      Lp ℝ 2 (muFull.restrict (closure (centeredCube
        (qc) (qs) hr :
        Set (SpatialCoordinates d)))))
    (hT : SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr
        (muFull.restrict (closure (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))))
        K C T)
    (hKCnn : 0 ≤ K ∧ 0 ≤ C)
    (i : (u : DomainL2 (centeredCube (qc)
          (qs) hr)) →
      (limitFormEnergy G u).toENNReal ≠ ⊤ →
      CubeFractionalL2 (k := 1) hd (qc)
        (qs) hr halfFractionalOrder)
    (hi : ∀ (u : DomainL2 (centeredCube (qc)
          (qs) hr))
      (hu : (limitFormEnergy G u).toENNReal ≠ ⊤), (i u hu).val 0 = u)
    (J : DomainL2 (centeredCube (qc)
        (qs) hr) → SpatialCoordinates d → ℝ)
    (hJ : ∀ (u : DomainL2 (centeredCube (qc)
          (qs) hr))
      (hu : (limitFormEnergy G u).toENNReal ≠ ⊤),
      (J u) =ᵐ[muFull.restrict (closure (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d)))]
        (T (i u hu) : SpatialCoordinates d → ℝ))
    (lam : ℝ) (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (ustar : DomainL2 (centeredCube (qc)
        (qs) hr))
    (hustar_ne : (limitFormEnergy G ustar).toENNReal ≠ ⊤)
    (hmin : ∀ w : DomainL2 (centeredCube (qc)
        (qs) hr),
      (limitFormEnergy G w).toENNReal ≠ ⊤ →
      (limitFormEnergy G ustar).toENNReal.toReal + lam * (∫ x, J ustar x ^ 2 ∂muFull.restrict
          (closure (centeredCube (qc)
            (qs) hr : Set (SpatialCoordinates d)))) -
        2 * ∫ x, f x * J ustar x ∂muFull.restrict (closure
          (centeredCube (qc)
            (qs) hr : Set (SpatialCoordinates d))) ≤
      (limitFormEnergy G w).toENNReal.toReal + lam * (∫ x, J w x ^ 2 ∂muFull.restrict
          (closure (centeredCube (qc)
            (qs) hr : Set (SpatialCoordinates d)))) -
        2 * ∫ x, f x * J w x ∂muFull.restrict (closure
          (centeredCube (qc)
            (qs) hr : Set (SpatialCoordinates d))))
    (huniq : ∀ w : DomainL2 (centeredCube (qc)
        (qs) hr),
      (limitFormEnergy G w).toENNReal ≠ ⊤ →
      (∀ v : DomainL2 (centeredCube (qc)
          (qs) hr),
        (limitFormEnergy G v).toENNReal ≠ ⊤ →
        (limitFormEnergy G w).toENNReal.toReal + lam * (∫ x, J w x ^ 2 ∂muFull.restrict
            (closure (centeredCube (qc)
              (qs) hr : Set (SpatialCoordinates d)))) -
          2 * ∫ x, f x * J w x ∂muFull.restrict (closure
            (centeredCube (qc)
              (qs) hr : Set (SpatialCoordinates d))) ≤
        (limitFormEnergy G v).toENNReal.toReal + lam * (∫ x, J v x ^ 2 ∂muFull.restrict
            (closure (centeredCube (qc)
              (qs) hr : Set (SpatialCoordinates d)))) -
          2 * ∫ x, f x * J v x ∂muFull.restrict (closure
            (centeredCube (qc)
              (qs) hr : Set (SpatialCoordinates d)))) →
      w = ustar)
    (RN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRNbound : ∀ (N : ℕ), ∀ x ∈ (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d)),
      |RN N omega lam f x| ≤ ‖f‖ / lam)
    (hRNzero : ∀ (N : ℕ), ∀ x ∈ frontier (closure (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d))),
      RN N omega lam f x = 0)
    (CHol : ℝ) (hCHol0 : 0 < CHol)
    (hHolderR : ∀ N, ∀ x ∈ closure (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d)),
      |RN N omega lam f x - RN N omega lam f y| ≤ CHol * dist x y ^ (1 / 4 : ℝ))
    (Region : Set (SpatialCoordinates d))
    (hNeighborhood : ∀ x ∈ closure ((centeredCube (qc)
        (qs) hr) : Set (SpatialCoordinates d)),
      Metric.ball x 1 ⊆ Region)
    (Kmu : ℝ) (hKmu0 : 0 ≤ Kmu) (epsilon : ℝ) (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (hgrowthBound : ∀ x ∈ Region, ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        muFull (Metric.ball x rr) ≤ ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)) ∧
          ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x rr) ≤
            ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)))
    (SInterp : CubeFractionalInterpolationInput d hd)
    (u : ℕ → killedSobolevGraph (centeredCube (qc)
        (qs) hr))
    (hfinite : ∀ N : ℕ,
      (RN N omega lam f =ᵐ[volume.restrict (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))]
        ((u N : SobolevData (centeredCube (qc)
          (qs) hr)).1 : SpatialCoordinates d → ℝ)) ∧
      (∀ w : killedSobolevGraph (centeredCube (qc)
          (qs) hr),
        sobolevCoefficientForm
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
            (u N : SobolevData (centeredCube (qc)
              (qs) hr))
            (w : SobolevData (centeredCube (qc)
              (qs) hr)) =
          ∫ x, (f x - lam * RN N omega lam f x) * (w : SobolevData
              (centeredCube (qc)
                (qs) hr)).1 x
            ∂((cutoffSpeedMeasure M H omega N).restrict (closure
              ((centeredCube (qc)
                (qs) hr) : Set (SpatialCoordinates d))))) ∧
      sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
          (u N : SobolevData (centeredCube (qc)
            (qs) hr))
          (u N : SobolevData (centeredCube (qc)
            (qs) hr)) ≤
        ‖f‖ ^ 2 * ((cutoffSpeedMeasure M H omega N).restrict (closure
            ((centeredCube (qc)
              (qs) hr) : Set (SpatialCoordinates d)))
          ((centeredCube (qc)
            (qs) hr) : Set (SpatialCoordinates d))).toReal
          / lam) :
    ∃ g : SpatialCoordinates d → ℝ,
      ContinuousOn g (closure (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (closure (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d))), g x = 0) ∧
      (∀ x ∈ closure (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d)),
        Filter.limsup (fun N => RN N omega lam f x) atTop = g x) ∧
      (∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
        ∀ x ∈ closure (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d)),
          |RN k omega lam f x - g x| < eps) ∧
      g =ᵐ[volume.restrict (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))]
        (ustar : SpatialCoordinates d → ℝ) := by
  set Kom : ℝ := max CHol (‖f‖ / lam) with hKomdef
  have hKom0 : 0 ≤ Kom := le_trans hCHol0.le (le_max_left _ _)
  have hbound : ∀ N, ∀ x ∈ closure (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d)),
      |RN N omega lam f x| ≤ Kom := by
    intro N x hx
    have hmapsto : Set.MapsTo (RN N omega lam f)
        (centeredCube (qc) (qs) hr :
          Set (SpatialCoordinates d))
        (Set.Icc (-(‖f‖ / lam)) (‖f‖ / lam)) :=
      fun y hy => abs_le.mp (hRNbound N y hy)
    have hcontN : ContinuousOn (RN N omega lam f)
        (closure (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))) :=
      aux_prop_uniform_resolvent_subsequence_bridge_holder_continuousOn
        (RN N omega lam f) (closure (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))) CHol hCHol0.le
        (hHolderR N)
    have hmapsto' := (hmapsto.closure_of_continuousOn hcontN) hx
    rw [(isClosed_Icc).closure_eq] at hmapsto'
    exact (abs_le.mpr hmapsto').trans (le_max_right _ _)
  have hcont : ∀ N, ContinuousOn (RN N omega lam f)
      (closure (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d))) := by
    intro N
    exact aux_prop_uniform_resolvent_subsequence_bridge_holder_continuousOn
      (RN N omega lam f) (closure (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d))) CHol hCHol0.le
      (hHolderR N)
  have hzero : ∀ N, ∀ x ∈ frontier (closure (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d))),
      RN N omega lam f x = 0 :=
    fun N => hRNzero N
  have hHolderR' : ∀ N, ∀ x ∈ closure (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d)),
      |RN N omega lam f x - RN N omega lam f y| ≤ Kom * dist x y ^ (1 / 4 : ℝ) := by
    intro N x hx y hy
    exact (hHolderR N x hx y hy).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hQbdd : Bornology.IsBounded (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d)) :=
    centeredCube_isBounded (qc) hr
  have hQopen : IsOpen (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d)) :=
    (centeredCube (qc) (qs) hr).isOpen
  have hQne : (centeredCube (qc)
      (qs) hr : Set (SpatialCoordinates d)).Nonempty :=
    aux_prop_speed_resolvent_cube_nonempty (qc) hr
  set K1' : ℝ := (1 + (qs) ^ (-(3 / 2 : ℝ))) * K1 with hK1'def
  have hK1'0 : 0 < K1' := by
    rw [hK1'def]; positivity
  have hc1' : ∀ N (v : killedSobolevGraph (centeredCube (qc)
      (qs) hr)),
      ∃ v3 : CubeFractionalL2 (k := 1) hd (qc)
          (qs) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
        v3.val 0 = (v : SobolevData (centeredCube (qc)
          (qs) hr)).1 ∧
        (cubeFractionalL2Norm hd (qc)
          (qs) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
          K1' * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
              (qc) hr)
            (v : SobolevData (centeredCube (qc)
              (qs) hr))
            (v : SobolevData (centeredCube (qc)
              (qs) hr)) := by
    intro N v
    obtain ⟨v3, hv30, hv3b⟩ := aux_car_variational_hcoer3_of_hc1 hd Sf
      (qc) (qs) hr
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
      K1 hK1.le v (hc1 N v)
    exact ⟨v3, hv30, by rw [hK1'def, mul_assoc]; exact hv3b⟩
  have hidentify : ∀ g : C(SpatialCoordinates d, ℝ),
      (∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
          ∀ x ∈ closure (centeredCube (qc)
            (qs) hr : Set (SpatialCoordinates d)),
            |RN (σ k) omega lam f x - g x| < eps) →
      (g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (qc) (qs)
            hr : Set (SpatialCoordinates d))]
        (ustar : SpatialCoordinates d → ℝ) := by
    intro g ⟨σ, hσ, hunif⟩
    have hmosco := inputs_classical_mosco_liminf hP
      (fun N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
      G hG
    exact aux_mfd_prop_as_forms_hidentify_at_omega hd epsilon hepsilon' qc qs hr M H omega Region
      hNeighborhood muFull hmuFull1 Kmu hKmu0 hgrowthBound
      (fun u => (limitFormEnergy G u).toENNReal) hmosco
      T K C ⟨hKCnn.1, hKCnn.2, hT⟩ i hi J hJ lam hlam f
      ustar ⟨hustar_ne, hmin, huniq⟩ u (fun N => RN N omega lam f) hfinite K1' hK1'0 hc1' SInterp
      g σ hσ hunif
  obtain ⟨g, hgcont, hgzero, hglimsup, hgunif, _hgHolder, hgustar⟩ :=
    aux_car_variational_full_convergence_of_hidentify
      (centeredCube (qc) (qs) hr :
        Set (SpatialCoordinates d)) hQopen hQne hQbdd (fun N => RN N omega lam f) ustar hcont hzero
      Kom hKom0 hbound hHolderR' hidentify
  exact ⟨g, hgcont, hgzero, hglimsup, hgunif, hgustar⟩

theorem aux_mfd_prop_as_forms_hFullConv
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHI : InfraredCharacterization M H)
    (qc : SpatialCoordinates d) (qs : ℝ) (hr : 0 < qs)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (qc)
        (qs) hr),
      ‖(v : SobolevData (centeredCube (qc)
          (qs) hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube
          (qc) (qs) hr)) v‖)
    (G : BilateralField d → DomainL2 (centeredCube (qc)
        (qs) hr) →L[ℝ]
      DomainL2 (centeredCube (qc)
        (qs) hr))
    (hG_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ f : DomainL2 (centeredCube (qc)
          (qs) hr),
        Tendsto (fun N : ℕ =>
          (responseSolution (killedResponseSpace (Ω := centeredCube
                (qc) (qs) hr) hP)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
              ((sobolevVolumeLoad f).comp
                (killedResponseSpace (Ω := centeredCube (qc)
                  (qs) hr) hP).space.subtypeL)).val.1)
          atTop (𝓝 (G omega f)))
    (hK1_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K1 : ℝ, 0 < K1 ∧
      ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube (qc)
          (qs) hr)),
        cubeFractionalSqNorm hd (qc)
            (qs) hr threeQuarterOrder
            (v : SobolevData (centeredCube (qc)
              (qs) hr)).1 ≤
          K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
              (qc) hr)
            (v : SobolevData (centeredCube (qc)
              (qs) hr))
            (v : SobolevData (centeredCube (qc)
              (qs) hr)))
    (muFull : BilateralField d → Measure (SpatialCoordinates d))
    (hmuFull_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
      muFull omega (frontier (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))) = 0 ∧
      muFull omega (closure (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))) < ⊤)
    (K C : BilateralField d → ℝ)
    (T : (omega : BilateralField d) → CubeFractionalL2 (k := 1) hd
        (qc) (qs) hr
        halfFractionalOrder →
      Lp ℝ 2 ((muFull omega).restrict (closure (centeredCube
        (qc) (qs) hr :
        Set (SpatialCoordinates d)))))
    (hT_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr
        ((muFull omega).restrict (closure (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))))
        (K omega) (C omega) (T omega))
    (hKCnn_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, 0 ≤ K omega ∧ 0 ≤ C omega)
    (i : (omega : BilateralField d) →
        (u : DomainL2 (centeredCube (qc)
              (qs) hr)) →
          (limitFormEnergy (G omega) u).toENNReal ≠ ⊤ →
          CubeFractionalL2 (k := 1) hd (qc)
            (qs) hr halfFractionalOrder)
    (hi_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (u : DomainL2 (centeredCube (qc)
            (qs) hr))
        (hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤), (i omega u hu).val 0 = u)
    (J : (omega : BilateralField d) → DomainL2 (centeredCube (qc)
        (qs) hr) → SpatialCoordinates d → ℝ)
    (hJ_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (u : DomainL2 (centeredCube (qc)
            (qs) hr))
        (hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤),
        (J omega u) =ᵐ[(muFull omega).restrict (closure (centeredCube
            (qc) (qs) hr :
            Set (SpatialCoordinates d)))] (T omega (i omega u hu) : SpatialCoordinates d → ℝ))
    (hKtr_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ Ktr : ℝ, 0 ≤ Ktr ∧
      ∀ (u : DomainL2 (centeredCube (qc)
            (qs) hr))
        (_hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤),
        (∫⁻ x, ENNReal.ofReal (J omega u x ^ 2)
            ∂((muFull omega).restrict (closure (centeredCube (qc)
              (qs) hr : Set (SpatialCoordinates d))))) ≤
          ENNReal.ofReal Ktr * (limitFormEnergy (G omega) u).toENNReal)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ N omega x, Measure.map LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (hLlocal_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega))
    (RN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN_formula : ∀ (N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d),
      RN N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (qc)
                (qs) hr : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x)))
    (hRNbound : ∀ (N : ℕ) (omega : BilateralField d) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x ∈ (centeredCube (qc)
            (qs) hr : Set (SpatialCoordinates d)),
          |RN N omega lam f x| ≤ ‖f‖ / lam)
    (hRNzero_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ x ∈ frontier (closure (centeredCube (qc)
            (qs) hr : Set (SpatialCoordinates d))),
            RN N omega lam f x = 0)
    (epsilon : ℝ) (_hepsilon : epsilon ∈ Set.Ioo (0 : ℝ) 1)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (Region : Set (SpatialCoordinates d))
    (hNeighborhood : ∀ x ∈ closure ((centeredCube (qc)
        (qs) hr) : Set (SpatialCoordinates d)),
      Metric.ball x 1 ⊆ Region)
    (hGrowth_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ Kmu : ℝ, 0 ≤ Kmu ∧
      ∀ x ∈ Region, ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        muFull omega (Metric.ball x rr) ≤ ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)) ∧
          ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x rr) ≤
            ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)))
    (hHolderAll_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ),
            ∀ x ∈ closure ((centeredCube (qc)
                (qs) hr) : Set (SpatialCoordinates d)),
            ∀ y ∈ closure ((centeredCube (qc)
                (qs) hr) : Set (SpatialCoordinates d)),
              |RN N omega lam f x - RN N omega lam f y| ≤ C * dist x y ^ (1 / 4 : ℝ))
    (SInterp : CubeFractionalInterpolationInput d hd) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∃ ustar : DomainL2 (centeredCube (qc)
              (qs) hr),
            ((limitFormEnergy (G omega) ustar).toENNReal ≠ ⊤ ∧
            (∀ w : DomainL2 (centeredCube (qc)
                (qs) hr),
              (limitFormEnergy (G omega) w).toENNReal ≠ ⊤ →
              (limitFormEnergy (G omega) ustar).toENNReal.toReal +
                  lam * (∫ x, J omega ustar x ^ 2 ∂((muFull omega).restrict (closure
                    (centeredCube (qc)
                      (qs) hr : Set (SpatialCoordinates d))))) -
                2 * ∫ x, f x * J omega ustar x ∂((muFull omega).restrict (closure
                    (centeredCube (qc)
                      (qs) hr : Set (SpatialCoordinates d)))) ≤
              (limitFormEnergy (G omega) w).toENNReal.toReal +
                  lam * (∫ x, J omega w x ^ 2 ∂((muFull omega).restrict (closure
                    (centeredCube (qc)
                      (qs) hr : Set (SpatialCoordinates d))))) -
                2 * ∫ x, f x * J omega w x ∂((muFull omega).restrict (closure
                    (centeredCube (qc)
                      (qs) hr : Set (SpatialCoordinates d))))) ∧
            (∀ w : DomainL2 (centeredCube (qc)
                (qs) hr),
              (limitFormEnergy (G omega) w).toENNReal ≠ ⊤ →
              (∀ v : DomainL2 (centeredCube (qc)
                  (qs) hr),
                (limitFormEnergy (G omega) v).toENNReal ≠ ⊤ →
                (limitFormEnergy (G omega) w).toENNReal.toReal +
                    lam * (∫ x, J omega w x ^ 2 ∂((muFull omega).restrict (closure
                      (centeredCube (qc)
                        (qs) hr : Set (SpatialCoordinates d))))) -
                  2 * ∫ x, f x * J omega w x ∂((muFull omega).restrict (closure
                      (centeredCube (qc)
                        (qs) hr : Set (SpatialCoordinates d)))) ≤
                (limitFormEnergy (G omega) v).toENNReal.toReal +
                    lam * (∫ x, J omega v x ^ 2 ∂((muFull omega).restrict (closure
                      (centeredCube (qc)
                        (qs) hr : Set (SpatialCoordinates d))))) -
                  2 * ∫ x, f x * J omega v x ∂((muFull omega).restrict (closure
                      (centeredCube (qc)
                        (qs) hr : Set (SpatialCoordinates d))))) →
              w = ustar)) ∧
            ∃ g : SpatialCoordinates d → ℝ,
              ContinuousOn g (closure (centeredCube (qc)
                (qs) hr : Set (SpatialCoordinates d))) ∧
              (∀ x ∈ frontier (closure (centeredCube (qc)
                (qs) hr : Set (SpatialCoordinates d))),
                g x = 0) ∧
              (∀ x ∈ closure (centeredCube (qc)
                (qs) hr : Set (SpatialCoordinates d)),
                Filter.limsup (fun N => RN N omega lam f x) atTop = g x) ∧
              (∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
                ∀ x ∈ closure (centeredCube (qc)
                  (qs) hr : Set (SpatialCoordinates d)),
                  |RN k omega lam f x - g x| < eps) ∧
              g =ᵐ[volume.restrict (centeredCube (qc)
                  (qs) hr : Set (SpatialCoordinates d))]
                (ustar : SpatialCoordinates d → ℝ) := by
  filter_upwards [hG_ae, hK1_ae, hmuFull_ae, hT_ae, hKCnn_ae, hi_ae, hJ_ae, hKtr_ae, hLlocal_ae,
    hRNzero_ae, hGrowth_ae, hHolderAll_ae]
    with omega hG hK1all hmuFull1 hT hKCnn hi hJ hKtrall hLlocal hRNzero hGrowth1 hHolderAll1
  intro lam hlam f
  obtain ⟨K1, hK1, hc1⟩ := hK1all
  obtain ⟨Ktr, hKtr, hJtr⟩ := hKtrall
  have hmufin' : ((muFull omega).restrict (closure (centeredCube
      (qc) (qs) hr :
      Set (SpatialCoordinates d)))) Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]; exact hmuFull1.2.2
  obtain ⟨ustar, hustar_ne, hmin, huniq⟩ :=
    aux_mfd_prop_as_forms_variational_step hd Sf M H hHI omega qc qs hr hP (G omega) hG K1 hK1
      hc1 ((muFull omega).restrict (closure (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d))))
      (muFull omega) rfl hmufin' (K omega) (C omega) (T omega) hT (i omega) hi (J omega) hJ
      Ktr hKtr hJtr lam hlam f
  refine ⟨ustar, ⟨hustar_ne, hmin, huniq⟩, ?_⟩
  have hpack : ∀ N : ℕ, ∃ u0 : killedSobolevGraph (centeredCube (qc)
      (qs) hr),
      (RN N omega lam f =ᵐ[volume.restrict (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))]
        ((u0 : SobolevData (centeredCube (qc)
          (qs) hr)).1 : SpatialCoordinates d → ℝ)) ∧
      (∀ w : killedSobolevGraph (centeredCube (qc)
          (qs) hr),
        sobolevCoefficientForm
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
            (u0 : SobolevData (centeredCube (qc)
              (qs) hr))
            (w : SobolevData (centeredCube (qc)
              (qs) hr)) =
          ∫ x, (f x - lam * RN N omega lam f x) * (w : SobolevData
              (centeredCube (qc)
                (qs) hr)).1 x
            ∂((cutoffSpeedMeasure M H omega N).restrict (closure
              ((centeredCube (qc)
                (qs) hr) : Set (SpatialCoordinates d))))) ∧
      sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
          (u0 : SobolevData (centeredCube (qc)
            (qs) hr))
          (u0 : SobolevData (centeredCube (qc)
            (qs) hr)) ≤
        ‖f‖ ^ 2 * ((cutoffSpeedMeasure M H omega N).restrict (closure
            ((centeredCube (qc)
              (qs) hr) : Set (SpatialCoordinates d)))
          ((centeredCube (qc)
            (qs) hr) : Set (SpatialCoordinates d))).toReal
          / lam := fun N => by
    have := hKN N
    exact aux_car_variational_hpack_at_N hd M H omega N KN L (hL N) (hLlocal N)
      (qc) (qs) hr lam hlam f
      RN hRN_formula (hRNbound N omega lam hlam f)
  choose u hfinite using hpack
  obtain ⟨CHol, hCHol0, hHolderR⟩ := hHolderAll1 lam hlam f
  obtain ⟨Kmu, hKmu0, hgrowthBound⟩ := hGrowth1
  exact aux_mfd_prop_as_forms_hidentify_and_converge hd Sf M H qc qs hr hP omega (G omega) hG K1 hK1
    hc1 (muFull omega) hmuFull1 (K omega) (C omega) (T omega) hT hKCnn (i omega) hi (J omega) hJ
    lam hlam f ustar hustar_ne hmin huniq RN (fun N => hRNbound N omega lam hlam f)
    (fun N => hRNzero N lam hlam f) CHol hCHol0 hHolderR Region hNeighborhood Kmu hKmu0 epsilon
    hepsilon' hgrowthBound SInterp u hfinite

theorem aux_mfd_prop_as_forms_hUniform_hVariational
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHI : InfraredCharacterization M H)
    (qc : SpatialCoordinates d) (qs : ℝ) (hr : 0 < qs)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (qc)
        (qs) hr),
      ‖(v : SobolevData (centeredCube (qc)
          (qs) hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube
          (qc) (qs) hr)) v‖)
    (G : BilateralField d → DomainL2 (centeredCube (qc)
        (qs) hr) →L[ℝ]
      DomainL2 (centeredCube (qc)
        (qs) hr))
    (hG_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ f : DomainL2 (centeredCube (qc)
          (qs) hr),
        Tendsto (fun N : ℕ =>
          (responseSolution (killedResponseSpace (Ω := centeredCube
                (qc) (qs) hr) hP)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc) hr)
              ((sobolevVolumeLoad f).comp
                (killedResponseSpace (Ω := centeredCube (qc)
                  (qs) hr) hP).space.subtypeL)).val.1)
          atTop (𝓝 (G omega f)))
    (hK1_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K1 : ℝ, 0 < K1 ∧
      ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube (qc)
          (qs) hr)),
        cubeFractionalSqNorm hd (qc)
            (qs) hr threeQuarterOrder
            (v : SobolevData (centeredCube (qc)
              (qs) hr)).1 ≤
          K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
              (qc) hr)
            (v : SobolevData (centeredCube (qc)
              (qs) hr))
            (v : SobolevData (centeredCube (qc)
              (qs) hr)))
    (muFull : BilateralField d → Measure (SpatialCoordinates d))
    (hmuFull_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
      muFull omega (frontier (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))) = 0 ∧
      muFull omega (closure (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))) < ⊤)
    (K C : BilateralField d → ℝ)
    (T : (omega : BilateralField d) → CubeFractionalL2 (k := 1) hd
        (qc) (qs) hr
        halfFractionalOrder →
      Lp ℝ 2 ((muFull omega).restrict (closure (centeredCube
        (qc) (qs) hr :
        Set (SpatialCoordinates d)))))
    (hT_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr
        ((muFull omega).restrict (closure (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))))
        (K omega) (C omega) (T omega))
    (hKCnn_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, 0 ≤ K omega ∧ 0 ≤ C omega)
    (i : (omega : BilateralField d) →
        (u : DomainL2 (centeredCube (qc)
              (qs) hr)) →
          (limitFormEnergy (G omega) u).toENNReal ≠ ⊤ →
          CubeFractionalL2 (k := 1) hd (qc)
            (qs) hr halfFractionalOrder)
    (hi_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (u : DomainL2 (centeredCube (qc)
            (qs) hr))
        (hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤), (i omega u hu).val 0 = u)
    (J : (omega : BilateralField d) → DomainL2 (centeredCube (qc)
        (qs) hr) → SpatialCoordinates d → ℝ)
    (hJ_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (u : DomainL2 (centeredCube (qc)
            (qs) hr))
        (hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤),
        (J omega u) =ᵐ[(muFull omega).restrict (closure (centeredCube
            (qc) (qs) hr :
            Set (SpatialCoordinates d)))] (T omega (i omega u hu) : SpatialCoordinates d → ℝ))
    (hKtr_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ Ktr : ℝ, 0 ≤ Ktr ∧
      ∀ (u : DomainL2 (centeredCube (qc)
            (qs) hr))
        (_hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤),
        (∫⁻ x, ENNReal.ofReal (J omega u x ^ 2)
            ∂((muFull omega).restrict (closure (centeredCube (qc)
              (qs) hr : Set (SpatialCoordinates d))))) ≤
          ENNReal.ofReal Ktr * (limitFormEnergy (G omega) u).toENNReal)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ N omega x, Measure.map LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (hLlocal_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega))
    (RN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN_formula : ∀ (N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d),
      RN N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (qc)
                (qs) hr : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x)))
    (hRNbound : ∀ (N : ℕ) (omega : BilateralField d) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x ∈ (centeredCube (qc)
            (qs) hr : Set (SpatialCoordinates d)),
          |RN N omega lam f x| ≤ ‖f‖ / lam)
    (hRNzero_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ x ∈ frontier (closure (centeredCube (qc)
            (qs) hr : Set (SpatialCoordinates d))),
            RN N omega lam f x = 0)
    (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioo (0 : ℝ) 1)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (Region : Set (SpatialCoordinates d))
    (hNeighborhood : ∀ x ∈ closure ((centeredCube (qc)
        (qs) hr) : Set (SpatialCoordinates d)),
      Metric.ball x 1 ⊆ Region)
    (hGrowth_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ Kmu : ℝ, 0 ≤ Kmu ∧
      ∀ x ∈ Region, ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        muFull omega (Metric.ball x rr) ≤ ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)) ∧
          ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x rr) ≤
            ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)))
    (hHolderAll_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ),
            ∀ x ∈ closure ((centeredCube (qc)
                (qs) hr) : Set (SpatialCoordinates d)),
            ∀ y ∈ closure ((centeredCube (qc)
                (qs) hr) : Set (SpatialCoordinates d)),
              |RN N omega lam f x - RN N omega lam f y| ≤ C * dist x y ^ (1 / 4 : ℝ))
    (SInterp : CubeFractionalInterpolationInput d hd) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      (∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ delta : ℝ, 0 < delta → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            ∀ x ∈ closure (centeredCube (qc)
              (qs) hr : Set (SpatialCoordinates d)),
              |RN N omega lam f x -
                Filter.limsup (fun N => RN N omega lam f x) atTop| < delta) ∧
      (∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∃ ustar : DomainL2 (centeredCube (qc)
              (qs) hr),
            (limitFormEnergy (G omega) ustar).toENNReal ≠ ⊤ ∧
            (fun x => Filter.limsup (fun N => RN N omega lam f x) atTop) =ᵐ[volume.restrict
                (centeredCube (qc)
                  (qs) hr : Set (SpatialCoordinates d))]
              (ustar : SpatialCoordinates d → ℝ) ∧
            (∀ w : DomainL2 (centeredCube (qc)
                (qs) hr),
              (limitFormEnergy (G omega) w).toENNReal ≠ ⊤ →
              (limitFormEnergy (G omega) ustar).toENNReal.toReal + lam * (∫ x, J omega ustar x ^ 2 ∂(muFull omega).restrict
                  (closure (centeredCube (qc)
                    (qs) hr : Set (SpatialCoordinates d)))) -
                2 * ∫ x, f x * J omega ustar x ∂(muFull omega).restrict (closure
                  (centeredCube (qc)
                    (qs) hr : Set (SpatialCoordinates d))) ≤
              (limitFormEnergy (G omega) w).toENNReal.toReal + lam * (∫ x, J omega w x ^ 2 ∂(muFull omega).restrict
                  (closure (centeredCube (qc)
                    (qs) hr : Set (SpatialCoordinates d)))) -
                2 * ∫ x, f x * J omega w x ∂(muFull omega).restrict (closure
                  (centeredCube (qc)
                    (qs) hr : Set (SpatialCoordinates d)))) ∧
            (∀ w : DomainL2 (centeredCube (qc)
                (qs) hr),
              (limitFormEnergy (G omega) w).toENNReal ≠ ⊤ →
              (∀ v : DomainL2 (centeredCube (qc)
                  (qs) hr),
                (limitFormEnergy (G omega) v).toENNReal ≠ ⊤ →
                (limitFormEnergy (G omega) w).toENNReal.toReal + lam * (∫ x, J omega w x ^ 2 ∂(muFull omega).restrict
                    (closure (centeredCube (qc)
                      (qs) hr : Set (SpatialCoordinates d)))) -
                  2 * ∫ x, f x * J omega w x ∂(muFull omega).restrict (closure
                    (centeredCube (qc)
                      (qs) hr : Set (SpatialCoordinates d))) ≤
                (limitFormEnergy (G omega) v).toENNReal.toReal + lam * (∫ x, J omega v x ^ 2 ∂(muFull omega).restrict
                    (closure (centeredCube (qc)
                      (qs) hr : Set (SpatialCoordinates d)))) -
                  2 * ∫ x, f x * J omega v x ∂(muFull omega).restrict (closure
                    (centeredCube (qc)
                      (qs) hr : Set (SpatialCoordinates d)))) →
              w = ustar)) := by
  have hFC := aux_mfd_prop_as_forms_hFullConv hd Sf M H hHI qc qs hr hP G hG_ae hK1_ae muFull
    hmuFull_ae K C T hT_ae hKCnn_ae i hi_ae J hJ_ae hKtr_ae KN hKN L hL hLlocal_ae RN hRN_formula
    hRNbound hRNzero_ae epsilon hepsilon hepsilon' Region hNeighborhood hGrowth_ae hHolderAll_ae
    SInterp
  filter_upwards [hFC] with omega hfc
  refine ⟨fun lam hlam f delta hdelta => ?_, fun lam hlam f => ?_⟩
  · obtain ⟨ustar, _, g, hgcont, hgzero, hglimsup, hgunif, hgustar⟩ := hfc lam hlam f
    obtain ⟨N0, hN0⟩ := hgunif delta hdelta
    refine ⟨N0, fun N hN x hx => ?_⟩
    rw [hglimsup x hx]
    exact hN0 N hN x hx
  · obtain ⟨ustar, ⟨hustar_ne, hmin, huniq⟩, g, hgcont, hgzero, hglimsup, hgunif, hgustar⟩ :=
      hfc lam hlam f
    refine ⟨ustar, hustar_ne, ?_, hmin, huniq⟩
    have hRneq : ∀ x ∈ (centeredCube (qc)
        (qs) hr : Set (SpatialCoordinates d)),
        Filter.limsup (fun N => RN N omega lam f x) atTop = g x := fun x hx =>
      hglimsup x (subset_closure hx)
    have hae1 : (fun x => Filter.limsup (fun N => RN N omega lam f x) atTop) =ᵐ[volume.restrict
        (centeredCube (qc)
          (qs) hr : Set (SpatialCoordinates d))] g :=
      Filter.eventuallyEq_of_mem (self_mem_ae_restrict
        (centeredCube (qc)
          (qs) hr).isOpen.measurableSet) hRneq
    exact hae1.trans hgustar

theorem aux_mfd_prop_as_forms_hFixedCube_glue
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Interp : CubeFractionalInterpolationInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHI : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : in_crossing M H PN KN)
    (qc : ℕ → SpatialCoordinates d) (qs : ℕ → ℝ)
    (hr : ∀ n : ℕ, 0 < qs n)
    (hP : ∀ n : ℕ, ∃ K : ℝ≥0,
        ∀ v : killedSobolevGraph (centeredCube (qc n)
            (qs n) (hr n)),
          ‖(v : SobolevData (centeredCube (qc n)
              (qs n) (hr n))).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube
              (qc n) (qs n)
              (hr n))) v‖)
    (G : (n : ℕ) → BilateralField d →
        (DomainL2 (centeredCube (qc n)
            (qs n) (hr n)) →L[ℝ]
          DomainL2 (centeredCube (qc n)
            (qs n) (hr n))))
    (hGtendsto : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (f : DomainL2 (centeredCube (qc n)
          (qs n) (hr n))),
        Tendsto
          (fun N : ℕ =>
            (responseSolution (killedResponseSpace (Ω := centeredCube
                  (qc n) (qs n)
                  (hr n)) (hP n))
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                  (qc n) (hr n))
                ((sobolevVolumeLoad f).comp
                  (killedResponseSpace (Ω := centeredCube (qc n)
                    (qs n) (hr n)) (hP n)).space.subtypeL)).val.1)
          atTop (𝓝 (G n omega f)))
    (muFull : BilateralField d → Measure (SpatialCoordinates d))
    (hmuFull : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
      (∀ n : ℕ, muFull omega (frontier (centeredCube (qc n)
          (qs n) (hr n) : Set (SpatialCoordinates d))) = 0) ∧
      (∀ n : ℕ, muFull omega (closure (centeredCube (qc n)
          (qs n) (hr n) : Set (SpatialCoordinates d))) < ⊤))
    (T : (n : ℕ) → (omega : BilateralField d) →
        CubeFractionalL2 (k := 1) hd (qc n)
          (qs n) (hr n) halfFractionalOrder →
        Lp ℝ 2 ((muFull omega).restrict (closure (centeredCube (qc n)
          (qs n) (hr n) : Set (SpatialCoordinates d)))))
    (Ktrace Ctrace : ℕ → BilateralField d → ℝ)
    (hT : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ n : ℕ, 0 ≤ Ktrace n omega ∧ 0 ≤ Ctrace n omega ∧
        SubdiffusiveProcess.Section9.CubeTraceCharacterization hd (qc n) (hr n)
          ((muFull omega).restrict (closure (centeredCube (qc n)
            (qs n) (hr n) : Set (SpatialCoordinates d))))
          (Ktrace n omega) (Ctrace n omega) (T n omega))
    (i : (n : ℕ) → (omega : BilateralField d) →
        (u : DomainL2 (centeredCube (qc n)
            (qs n) (hr n))) →
        (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤ →
        CubeFractionalL2 (k := 1) hd (qc n)
          (qs n) (hr n) halfFractionalOrder)
    (h_i_val : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (u : DomainL2 (centeredCube (qc n)
            (qs n) (hr n)))
        (hu : (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤),
        (i n omega u hu).val 0 = u)
    (J : (n : ℕ) → BilateralField d → DomainL2 (centeredCube (qc n)
        (qs n) (hr n)) → SpatialCoordinates d → ℝ)
    (hJ : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (u : DomainL2 (centeredCube (qc n)
            (qs n) (hr n)))
        (hu : (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤),
        (J n omega u) =ᵐ[(muFull omega).restrict (closure (centeredCube
            (qc n) (qs n)
            (hr n) : Set (SpatialCoordinates d)))]
          (T n omega (i n omega u hu) : SpatialCoordinates d → ℝ))
    (RN : ℕ → ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN_formula : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
        (x : SpatialCoordinates d),
      RN n N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (qc n)
                (qs n) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x)))
    (n0 : ℕ)
    (hHolder :
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        -- Piggy-backs the `lem_as_coarse` fractional coercivity constant already computed
        -- internally below (`K1`/`hcf`), so `car_variational` gets it for free from this
        -- already-paid-for call instead of re-invoking `lem_as_coarse` at car_variational's
        -- own top level (which is expensive enough there to breach the 200000-heartbeat
        -- ceiling on the whole `car_variational` declaration; see NOTES.md).
        (∃ K1 : ℝ, 0 < K1 ∧ ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube
              (qc n0) (qs n0)
              (hr n0))),
          cubeFractionalSqNorm hd (qc n0)
              (qs n0) (hr n0) threeQuarterOrder
              (v : SobolevData (centeredCube (qc n0)
                (qs n0) (hr n0))).1 ≤
            K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (qc n0) (hr n0))
              (v : SobolevData (centeredCube (qc n0)
                (qs n0) (hr n0)))
              (v : SobolevData (centeredCube (qc n0)
                (qs n0) (hr n0)))) ∧
        ∀ (lam0 lam1 : ℝ), 0 < lam0 → lam0 ≤ lam1 →
          ∃ Kom : ℝ, 0 < Kom ∧ ∀ (N : ℕ) (lam : ℝ), lam0 ≤ lam → lam ≤ lam1 →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ‖f‖ ≤ 1 →
              (∀ x ∈ closure (centeredCube (qc n0)
                  (qs n0) (hr n0) : Set (SpatialCoordinates d)),
                |RN n0 N omega lam f x| ≤ Kom) ∧
              ∀ x ∈ closure (centeredCube (qc n0)
                  (qs n0) (hr n0) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure (centeredCube (qc n0)
                  (qs n0) (hr n0) : Set (SpatialCoordinates d)),
                |RN n0 N omega lam f x - RN n0 N omega lam f y| ≤
                  Kom * dist x y ^ (1 / 4 : ℝ)) 
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ N omega x, Measure.map LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega))
    (deltaGrowth : ℝ) (hMdeltaGrowth : M.delta ≤ deltaGrowth)
    (hGrowth_all : ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ deltaGrowth →
      ∃ mu : BilateralField d → Measure (SpatialCoordinates d),
        Measurable mu ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          MeasuresConvergeLocally (fun N ↦ weightedChaosCutoff M H N omega) (mu omega) ∧
          IsLocallyFiniteMeasure (mu omega) ∧
          (mu omega).IsOpenPosMeasure ∧ NullSingletonClass (mu omega) ∧
          (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
            mu omega (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0)) ∧
        ∀ (R : Set (SpatialCoordinates d)), Bornology.IsBounded R →
          ∃ Kmu : BilateralField d → ℝ,
            MemLp Kmu (↑(16 * d * (d + 2) + 1) : ℝ≥0∞) (chaosSampleLaw M).toMeasure ∧
            ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              0 ≤ Kmu omega ∧
              (∀ N x, x ∈ R → ∀ r, 0 < r → r ≤ 1 →
                weightedChaosCutoff M H N omega (Metric.ball x r) ≤
                  ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - 1 / (16 * ((d : ℝ) + 2))))) ∧
              (∀ x, x ∈ R → ∀ r, 0 < r → r ≤ 1 →
                mu omega (Metric.ball x r) ≤
                  ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - 1 / (16 * ((d : ℝ) + 2)))))) :
      let Q0 : Opens (SpatialCoordinates d) :=
        centeredCube (qc n0)
          (qs n0) (hr n0)
      let mu0 : BilateralField d → Measure (SpatialCoordinates d) :=
        fun omega => (muFull omega).restrict (closure (Q0 : Set (SpatialCoordinates d)))
      let Elim0 : BilateralField d → DomainL2 Q0 → ℝ≥0∞ :=
        fun omega u => (limitFormEnergy (G n0 omega) u).toENNReal
      let Func0 : BilateralField d → ℝ →
          BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          DomainL2 Q0 → ℝ :=
        fun omega lam f u =>
          (Elim0 omega u).toReal +
            lam * (∫ x, J n0 omega u x ^ 2 ∂(mu0 omega)) -
            2 * (∫ x, f x * J n0 omega u x ∂(mu0 omega))
      ∃ Rn : BilateralField d → ℝ →
          BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          SpatialCoordinates d → ℝ,
        (∀ (lam : ℝ), 0 < lam →
          ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
            Measurable (fun p : BilateralField d × SpatialCoordinates d =>
              Rn p.1 lam f p.2)) ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (∀ (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ContinuousOn (Rn omega lam f) (closure (Q0 : Set (SpatialCoordinates d))) ∧
              ∀ x ∈ frontier (Q0 : Set (SpatialCoordinates d)),
                Rn omega lam f x = 0) ∧
          (∀ (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ∀ delta : ℝ, 0 < delta → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
                ∀ x ∈ closure (Q0 : Set (SpatialCoordinates d)),
                  |RN n0 N omega lam f x - Rn omega lam f x| < delta) ∧
          (∀ (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ∃ ustar : DomainL2 Q0,
                Elim0 omega ustar ≠ ⊤ ∧
                (Rn omega lam f) =ᵐ[volume.restrict (Q0 : Set (SpatialCoordinates d))]
                  (ustar : SpatialCoordinates d → ℝ) ∧
                (∀ v : DomainL2 Q0,
                  Elim0 omega v ≠ ⊤ → Func0 omega lam f ustar ≤ Func0 omega lam f v) ∧
                (∀ v : DomainL2 Q0,
                  Elim0 omega v ≠ ⊤ →
                  (∀ w : DomainL2 Q0,
                    Elim0 omega w ≠ ⊤ → Func0 omega lam f v ≤ Func0 omega lam f w) →
                  v = ustar)))  := by
    let Q0 : Opens (SpatialCoordinates d) :=
      centeredCube (qc n0)
        (qs n0) (hr n0)
    let mu0 : BilateralField d → Measure (SpatialCoordinates d) :=
      fun omega => (muFull omega).restrict (closure (Q0 : Set (SpatialCoordinates d)))
    let Elim0 : BilateralField d → DomainL2 Q0 → ℝ≥0∞ :=
      fun omega u => (limitFormEnergy (G n0 omega) u).toENNReal
    let Func0 : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → DomainL2 Q0 → ℝ :=
      fun omega lam f u =>
        (Elim0 omega u).toReal +
            lam * (∫ x, J n0 omega u x ^ 2 ∂(mu0 omega)) -
            2 * (∫ x, f x * J n0 omega u x ∂(mu0 omega))
    let epsilonGrowth : ℝ := 1 / (16 * ((d : ℝ) + 2))
    let Region : Set (SpatialCoordinates d) :=
      Metric.ball (qc n0)
        (qs n0 / 2 + 1)
    have hRegion := aux_mfd_prop_as_forms_region
      (qc n0) (qs n0) (hr n0)
    obtain ⟨muChaos, hMuChaosMeas, hRegChaos, hGrowth⟩ := hGrowth_all M H hHI hMdeltaGrowth
    have hGrowthR := hGrowth Region hRegion.1
    obtain ⟨Kmu, hKmu0, hKmuBound⟩ := hGrowthR
    have hgrowthMuFull : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 ≤ K ∧
        ∀ x ∈ Region, ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
          muFull omega (Metric.ball x rr) ≤ ENNReal.ofReal (K * rr ^ ((d : ℝ) - epsilonGrowth)) ∧
            ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x rr) ≤
              ENNReal.ofReal (K * rr ^ ((d : ℝ) - epsilonGrowth)) := by
      filter_upwards [hKmuBound, hRegChaos, hmuFull] with omega hKb hRc hmF
      have : IsLocallyFiniteMeasure (muChaos omega) := hRc.2.1
      have : (muChaos omega).IsOpenPosMeasure := hRc.2.2.1
      exact ⟨Kmu omega, hKb.1,
        aux_car_variational_growth_muFull_bridge M H omega epsilonGrowth Region (muFull omega)
          (muChaos omega) hmF.1 hRc.1 (Kmu omega) hKb.1 hKb.2⟩
    clear hGrowth hKmuBound hRegChaos hMuChaosMeas muChaos Kmu hKmu0
      hGrowth_all hMdeltaGrowth deltaGrowth
    have hHolderAll := aux_mfd_prop_as_forms_holder_all qc qs hr M KN RN hRN_formula n0
      (hHolder.mono fun _ h => h.2)
    have hstart := aux_car_variational_path_start M H PN KN hin
    have hzeroOutside := aux_mfd_prop_as_forms_RN_zero_outside M qc qs hr KN
      hstart RN hRN_formula
    have hRNzero : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (lam : ℝ), 0 < lam →
          ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
            ∀ x ∈ frontier (closure (centeredCube
              (qc n0)
              (qs n0) (hr n0) : Set (SpatialCoordinates d))),
              RN n0 N omega lam f x = 0 := by
      filter_upwards [hzeroOutside] with omega hω
      intro N lam hlam f x hx
      apply hω n0 N lam hlam f x
      exact disjoint_left.1 (disjoint_frontier_iff_isOpen.mpr
        (centeredCube (qc n0)
          (qs n0) (hr n0)).isOpen) (
            frontier_closure_subset hx)
    have hRNbound := aux_mfd_prop_as_forms_RN_bound M qc qs hr KN hKN RN hRN_formula
    have hKtr_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ Ktr : ℝ, 0 ≤ Ktr ∧
        ∀ (u : DomainL2 Q0) (hu : Elim0 omega u ≠ ⊤),
          (∫⁻ x, ENNReal.ofReal (J n0 omega u x ^ 2) ∂mu0 omega) ≤
            ENNReal.ofReal Ktr * Elim0 omega u :=
      aux_mfd_prop_as_forms_Ktr_bound hd Sf Interp M H hHI (qc n0) (qs n0) (hr n0) (hP n0) (G n0)
        (hGtendsto.mono fun omega h f => h n0 f) (hHolder.mono fun omega h => h.1) muFull
        (Ktrace n0) (Ctrace n0) (T n0) (hT.mono fun omega h => ⟨(h n0).1, (h n0).2.1⟩)
        (hT.mono fun omega h => (h n0).2.2) (i n0) (h_i_val.mono fun omega h => h n0) (J n0)
        (hJ.mono fun omega h => h n0)
    have hepsGrowth := aux_car_variational_hol_cube_cutoff_holder_eps_choice hd
    have hepsilonIoo : epsilonGrowth ∈ Set.Ioo (0 : ℝ) 1 := by
      refine ⟨hepsGrowth.1, ?_⟩
      dsimp only [epsilonGrowth]
      apply (div_lt_one (by positivity)).2
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have hepsilon'8 : epsilonGrowth < 1 / (8 * ((d : ℝ) + 2)) := by
      dsimp only [epsilonGrowth]
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith
    have harg_G_ae := hGtendsto.mono fun omega h f => h n0 f
    have harg_K1_ae := hHolder.mono fun omega h => h.1
    have harg_muFull_ae := hmuFull.mono fun omega h => (⟨h.1, h.2.1 n0, h.2.2 n0⟩ :
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
      muFull omega (frontier (centeredCube (qc n0)
          (qs n0) (hr n0) : Set (SpatialCoordinates d))) = 0 ∧
      muFull omega (closure (centeredCube (qc n0)
          (qs n0) (hr n0) : Set (SpatialCoordinates d))) < ⊤)
    have harg_T_ae := hT.mono fun omega h => (h n0).2.2
    have harg_KCnn_ae := hT.mono fun omega h =>
      (⟨(h n0).1, (h n0).2.1⟩ : 0 ≤ Ktrace n0 omega ∧ 0 ≤ Ctrace n0 omega)
    have harg_i_ae := h_i_val.mono fun omega h => h n0
    have harg_J_ae := hJ.mono fun omega h => h n0
    clear hGtendsto hHolder hmuFull hT h_i_val hJ
    let Rn : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ :=
      fun omega lam f x => limsup (fun N => RN n0 N omega lam f x) atTop
    have hUV := aux_mfd_prop_as_forms_hUniform_hVariational hd Sf M H hHI (qc n0) (qs n0) (hr n0) (hP n0)
      (G n0) harg_G_ae harg_K1_ae muFull harg_muFull_ae (Ktrace n0) (Ctrace n0) (T n0)
      harg_T_ae harg_KCnn_ae (i n0) harg_i_ae (J n0) harg_J_ae hKtr_ae
      KN hKN L hL hLlocal (RN n0) (hRN_formula n0) (hRNbound n0) hRNzero
      epsilonGrowth hepsilonIoo hepsilon'8 Region hRegion.2 hgrowthMuFull hHolderAll Interp
    have hUniform : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (lam : ℝ), 0 < lam →
          ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
            ∀ delta : ℝ, 0 < delta → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
              ∀ x ∈ closure (Q0 : Set (SpatialCoordinates d)),
                |RN n0 N omega lam f x - Rn omega lam f x| < delta := by
      filter_upwards [hUV] with omega huv
      exact huv.1
    have hVariational : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (lam : ℝ), 0 < lam →
          ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
            ∃ ustar : DomainL2 Q0,
              Elim0 omega ustar ≠ ⊤ ∧
              (Rn omega lam f) =ᵐ[volume.restrict (Q0 : Set (SpatialCoordinates d))]
                (ustar : SpatialCoordinates d → ℝ) ∧
              (∀ v : DomainL2 Q0, Elim0 omega v ≠ ⊤ →
                Func0 omega lam f ustar ≤ Func0 omega lam f v) ∧
              (∀ v : DomainL2 Q0, Elim0 omega v ≠ ⊤ →
                (∀ w : DomainL2 Q0, Elim0 omega w ≠ ⊤ →
                  Func0 omega lam f v ≤ Func0 omega lam f w) →
                v = ustar) := by
      filter_upwards [hUV] with omega huv
      exact huv.2
    clear hUV harg_G_ae harg_K1_ae harg_muFull_ae harg_T_ae harg_KCnn_ae harg_i_ae harg_J_ae
      hKtr_ae hRNzero hRNbound hgrowthMuFull hRegion Region epsilonGrowth hepsilonIoo
      hepsilon'8 L hL hLlocal hepsGrowth
    have hRNmeas : ∀ (N : ℕ) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
        Measurable (fun p : BilateralField d × SpatialCoordinates d =>
          RN n0 N p.1 lam f p.2) := by
      intro N lam f
      have heq : (fun p : BilateralField d × SpatialCoordinates d =>
          RN n0 N p.1 lam f p.2) =
          (fun p : BilateralField d × SpatialCoordinates d =>
            ∫ path, (∫ t in Set.Ioi (0 : ℝ),
              Set.indicator
                {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                  (centeredCube (qc n0)
                    (qs n0) (hr n0) :
                      Set (SpatialCoordinates d)) path}
                (fun s : ℝ => Real.exp (-lam * s) * f
                  (path (Real.toNNReal s))) t) ∂(KN N p)) := by
        funext p
        rw [hRN_formula n0 N p.1 lam f p.2]
      rw [heq]
      exact aux_car_variational_occupation_measurable KN N (hKN N)
        (centeredCube (qc n0)
          (qs n0) (hr n0)) lam f
    have hRnMeas : ∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        Measurable (fun p : BilateralField d × SpatialCoordinates d =>
          Rn p.1 lam f p.2) := by
      intro lam hlam f
      dsimp [Rn]
      apply Measurable.limsup
      intro N
      exact hRNmeas N lam f
    have hcontAE := aux_mfd_prop_as_forms_RN_continuous qc qs hr RN n0 hHolderAll
    clear hP
    clear hin Ktrace
    clear PN Ctrace hstart i
    clear T hHI hHolderAll
    clear Sf Interp KN hKN hRN_formula
    have hRemaining := aux_car_variational_hRemaining_final M Q0 (Elim0)
      (Func0) (RN n0) Rn (fun omega lam f x => rfl) (hzeroOutside.mono fun omega h => h n0)
      hcontAE hUniform hVariational
    refine ⟨Rn, hRnMeas, ?_⟩
    simpa only [Q0, mu0, Elim0, Func0] using hRemaining


theorem aux_mfd_prop_as_forms_lift_supply
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {I : Type*} (qc : I → SpatialCoordinates d) (qs : I → ℝ) (hr : ∀ n, 0 < qs n)
    (G : (n : I) → BilateralField d →
          (DomainL2 (centeredCube (qc n)
              (qs n)
              (hr n)) →L[ℝ]
            DomainL2 (centeredCube (qc n)
              (qs n)
              (hr n))))
    (hco : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ n : I,
          (∀ u : DomainL2 (centeredCube (qc n)
              (qs n)
              (hr n)),
            limitFormEnergy (G n omega) u ≠ ⊤ →
            ∃ v : CubeFractionalL2 (k := 1) hd
                (qc n)
                (qs n)
                (hr n) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
              v.val 0 = u)) :
    ∃ i : (n : I) → (omega : BilateralField d) →
        (u : DomainL2 (centeredCube (qc n)
              (qs n)
              (hr n))) →
          (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤ →
          CubeFractionalL2 (k := 1) hd (qc n)
            (qs n)
            (hr n) halfFractionalOrder,
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (n : I) (u : DomainL2 (centeredCube (qc n)
              (qs n)
              (hr n)))
          (hu : (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤),
          (i n omega u hu).val 0 = u := by
  classical
  refine ⟨fun n omega u _ =>
    if h : cubeFractionalL2Seminorm hd (qc n)
        (qs n)
        (hr n) halfFractionalOrder (fun _ : Fin 1 => u) < ⊤
    then ⟨fun _ => u, h⟩
    else ⟨fun _ => 0, aux_mfd_convergence_seminorm_zero hd _ _ _ halfFractionalOrder⟩, ?_⟩
  filter_upwards [hco] with omega h
  intro n u hu
  have hne : limitFormEnergy (G n omega) u ≠ ⊤ := by
    intro htop
    apply hu
    rw [htop]
    rfl
  obtain ⟨v, hv⟩ := h n u hne
  have hv' : v.val = fun _ : Fin 1 => u := by
    funext j
    rw [Fin.fin_one_eq_zero j]
    exact hv
  have h34 : cubeFractionalL2Seminorm hd (qc n)
      (qs n)
      (hr n) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder (fun _ : Fin 1 => u) < ⊤ := by
    rw [← hv']
    exact v.property
  have h12 := aux_mfd_convergence_seminorm_mono hd _ _ _ halfFractionalOrder
    _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder (by
      simp only [halfFractionalOrder, _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder]
      norm_num) _ h34
  dsimp only [CubeFractionalL2]
  simp only [dite_eq_left h12]


/-- Choose completed speed traces on any fixed cube; bad samples use the zero map. -/
theorem aux_mfd_prop_as_forms_trace_supply {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (qc : SpatialCoordinates d) (qs : ℝ) (hr : 0 < qs)
    (muFull : BilateralField d → Measure (SpatialCoordinates d))
    (hmass : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      muFull omega (closure (centeredCube qc qs hr : Set (SpatialCoordinates d))) < ⊤)
    (hgr : ∃ K : BilateralField d → ℝ,
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, 0 ≤ K omega ∧
        ∀ x ∈ closure (centeredCube qc qs hr : Set (SpatialCoordinates d)),
          ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            muFull omega (Metric.ball x rr) ≤
              ENNReal.ofReal (K omega * rr ^ ((d : ℝ) - aux_mfd_convergence_eps d))) :
    ∃ (T : (omega : BilateralField d) →
        CubeFractionalL2 (k := 1) hd qc qs hr halfFractionalOrder →
          Lp ℝ 2 ((muFull omega).restrict
            (closure (centeredCube qc qs hr : Set (SpatialCoordinates d)))))
      (K C : BilateralField d → ℝ),
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, 0 ≤ K omega ∧ 0 ≤ C omega ∧
        SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr
          ((muFull omega).restrict (closure (centeredCube qc qs hr : Set (SpatialCoordinates d))))
          (K omega) (C omega) (T omega) := by
  classical
  obtain ⟨K, hK⟩ := hgr
  have hε := aux_mfd_convergence_eps_unit d
  have ht : (d : ℝ) - 1 < (d : ℝ) - aux_mfd_convergence_eps d := by linarith [hε.2]
  obtain ⟨C, hC, hcomplete⟩ := lem_19_trace_completion d hd qc qs hr
    ((d : ℝ) - aux_mfd_convergence_eps d) ht
  let Qbar : Set (SpatialCoordinates d) := closure (centeredCube qc qs hr : Set (SpatialCoordinates d))
  have hQbar : MeasurableSet Qbar := isClosed_closure.measurableSet
  have hTex : ∀ omega : BilateralField d,
      ∃ T : CubeFractionalL2 (k := 1) hd qc qs hr halfFractionalOrder →
          Lp ℝ 2 ((muFull omega).restrict Qbar),
        (0 ≤ K omega ∧ muFull omega Qbar < ⊤ ∧
          ∀ x ∈ Qbar, ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            muFull omega (Metric.ball x rr) ≤
              ENNReal.ofReal (K omega * rr ^ ((d : ℝ) - aux_mfd_convergence_eps d))) →
        SubdiffusiveProcess.Section9.CubeTraceCharacterization hd qc hr
          ((muFull omega).restrict Qbar) (K omega) C T := by
    intro omega
    by_cases hg : (0 ≤ K omega ∧ muFull omega Qbar < ⊤ ∧
          ∀ x ∈ Qbar, ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            muFull omega (Metric.ball x rr) ≤
              ENNReal.ofReal (K omega * rr ^ ((d : ℝ) - aux_mfd_convergence_eps d)))
    · have hfinite : ((muFull omega).restrict Qbar) Set.univ < ⊤ := by
        simpa only [Measure.restrict_apply_univ] using hg.2.1
      have hsupp : ((muFull omega).restrict Qbar) Qbarᶜ = 0 := by
        rw [Measure.restrict_apply hQbar.compl, Set.compl_inter_self, measure_empty]
      have hgrowth : ∀ x ∈ Qbar, ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
          ((muFull omega).restrict Qbar) (Metric.ball x rr) ≤
            ENNReal.ofReal (K omega * rr ^ ((d : ℝ) - aux_mfd_convergence_eps d)) := by
        intro x hx rr hr0 hr1
        exact (Measure.restrict_le_self _).trans (hg.2.2 x hx rr hr0 hr1)
      obtain ⟨T, hT, _⟩ := hcomplete ((muFull omega).restrict Qbar) (K omega)
        hfinite hsupp hg.1 hgrowth
      exact ⟨T, fun _ => ⟨hT.1, hT.2.1, hT.2.2.1⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hg⟩
  choose T hT using hTex
  refine ⟨T, K, fun _ => C, ?_⟩
  filter_upwards [hmass, hK] with omega hm hk
  exact ⟨hk.1, hC, hT omega ⟨hk.1, hm, hk.2⟩⟩


theorem aux_mfd_prop_as_forms_cube_glue_call
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Interp : CubeFractionalInterpolationInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHI : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : in_crossing M H PN KN)
    {I : Type*} (qc : I → SpatialCoordinates d) (qs : I → ℝ)
    (hr : ∀ n : I, 0 < qs n)
    (hP : ∀ n : I, ∃ K : ℝ≥0,
        ∀ v : killedSobolevGraph (centeredCube (qc n)
            (qs n) (hr n)),
          ‖(v : SobolevData (centeredCube (qc n)
              (qs n) (hr n))).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube
              (qc n) (qs n)
              (hr n))) v‖)
    (G : (n : I) → BilateralField d →
        (DomainL2 (centeredCube (qc n)
            (qs n) (hr n)) →L[ℝ]
          DomainL2 (centeredCube (qc n)
            (qs n) (hr n))))
    (hGtendsto : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : I) (f : DomainL2 (centeredCube (qc n)
          (qs n) (hr n))),
        Tendsto
          (fun N : ℕ =>
            (responseSolution (killedResponseSpace (Ω := centeredCube
                  (qc n) (qs n)
                  (hr n)) (hP n))
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                  (qc n) (hr n))
                ((sobolevVolumeLoad f).comp
                  (killedResponseSpace (Ω := centeredCube (qc n)
                    (qs n) (hr n)) (hP n)).space.subtypeL)).val.1)
          atTop (𝓝 (G n omega f)))
    (muFull : BilateralField d → Measure (SpatialCoordinates d))
    (hmuFull : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
      (∀ n : I, muFull omega (frontier (centeredCube (qc n)
          (qs n) (hr n) : Set (SpatialCoordinates d))) = 0) ∧
      (∀ n : I, muFull omega (closure (centeredCube (qc n)
          (qs n) (hr n) : Set (SpatialCoordinates d))) < ⊤))
    (T : (n : I) → (omega : BilateralField d) →
        CubeFractionalL2 (k := 1) hd (qc n)
          (qs n) (hr n) halfFractionalOrder →
        Lp ℝ 2 ((muFull omega).restrict (closure (centeredCube (qc n)
          (qs n) (hr n) : Set (SpatialCoordinates d)))))
    (Ktrace Ctrace : I → BilateralField d → ℝ)
    (hT : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ n : I, 0 ≤ Ktrace n omega ∧ 0 ≤ Ctrace n omega ∧
        SubdiffusiveProcess.Section9.CubeTraceCharacterization hd (qc n) (hr n)
          ((muFull omega).restrict (closure (centeredCube (qc n)
            (qs n) (hr n) : Set (SpatialCoordinates d))))
          (Ktrace n omega) (Ctrace n omega) (T n omega))
    (i : (n : I) → (omega : BilateralField d) →
        (u : DomainL2 (centeredCube (qc n)
            (qs n) (hr n))) →
        (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤ →
        CubeFractionalL2 (k := 1) hd (qc n)
          (qs n) (hr n) halfFractionalOrder)
    (h_i_val : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : I) (u : DomainL2 (centeredCube (qc n)
            (qs n) (hr n)))
        (hu : (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤),
        (i n omega u hu).val 0 = u)
    (J : (n : I) → BilateralField d → DomainL2 (centeredCube (qc n)
        (qs n) (hr n)) → SpatialCoordinates d → ℝ)
    (hJ : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : I) (u : DomainL2 (centeredCube (qc n)
            (qs n) (hr n)))
        (hu : (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤),
        (J n omega u) =ᵐ[(muFull omega).restrict (closure (centeredCube
            (qc n) (qs n)
            (hr n) : Set (SpatialCoordinates d)))]
          (T n omega (i n omega u hu) : SpatialCoordinates d → ℝ))
    (RN : I → ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN_formula : ∀ (n : I) (N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
        (x : SpatialCoordinates d),
      RN n N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (qc n)
                (qs n) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x)))
    (n0 : I)
    (hHolder :
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        -- Piggy-backs the `lem_as_coarse` fractional coercivity constant already computed
        -- internally below (`K1`/`hcf`), so `car_variational` gets it for free from this
        -- already-paid-for call instead of re-invoking `lem_as_coarse` at car_variational's
        -- own top level (which is expensive enough there to breach the 200000-heartbeat
        -- ceiling on the whole `car_variational` declaration; see NOTES.md).
        (∃ K1 : ℝ, 0 < K1 ∧ ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube
              (qc n0) (qs n0)
              (hr n0))),
          cubeFractionalSqNorm hd (qc n0)
              (qs n0) (hr n0) threeQuarterOrder
              (v : SobolevData (centeredCube (qc n0)
                (qs n0) (hr n0))).1 ≤
            K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (qc n0) (hr n0))
              (v : SobolevData (centeredCube (qc n0)
                (qs n0) (hr n0)))
              (v : SobolevData (centeredCube (qc n0)
                (qs n0) (hr n0)))) ∧
        ∀ (lam0 lam1 : ℝ), 0 < lam0 → lam0 ≤ lam1 →
          ∃ Kom : ℝ, 0 < Kom ∧ ∀ (N : ℕ) (lam : ℝ), lam0 ≤ lam → lam ≤ lam1 →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ‖f‖ ≤ 1 →
              (∀ x ∈ closure (centeredCube (qc n0)
                  (qs n0) (hr n0) : Set (SpatialCoordinates d)),
                |RN n0 N omega lam f x| ≤ Kom) ∧
              ∀ x ∈ closure (centeredCube (qc n0)
                  (qs n0) (hr n0) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure (centeredCube (qc n0)
                  (qs n0) (hr n0) : Set (SpatialCoordinates d)),
                |RN n0 N omega lam f x - RN n0 N omega lam f y| ≤
                  Kom * dist x y ^ (1 / 4 : ℝ)) 
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ N omega x, Measure.map LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega))
    (deltaGrowth : ℝ) (hMdeltaGrowth : M.delta ≤ deltaGrowth)
    (hGrowth_all : ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ deltaGrowth →
      ∃ mu : BilateralField d → Measure (SpatialCoordinates d),
        Measurable mu ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          MeasuresConvergeLocally (fun N ↦ weightedChaosCutoff M H N omega) (mu omega) ∧
          IsLocallyFiniteMeasure (mu omega) ∧
          (mu omega).IsOpenPosMeasure ∧ NullSingletonClass (mu omega) ∧
          (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
            mu omega (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0)) ∧
        ∀ (R : Set (SpatialCoordinates d)), Bornology.IsBounded R →
          ∃ Kmu : BilateralField d → ℝ,
            MemLp Kmu (↑(16 * d * (d + 2) + 1) : ℝ≥0∞) (chaosSampleLaw M).toMeasure ∧
            ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              0 ≤ Kmu omega ∧
              (∀ N x, x ∈ R → ∀ r, 0 < r → r ≤ 1 →
                weightedChaosCutoff M H N omega (Metric.ball x r) ≤
                  ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - 1 / (16 * ((d : ℝ) + 2))))) ∧
              (∀ x, x ∈ R → ∀ r, 0 < r → r ≤ 1 →
                mu omega (Metric.ball x r) ≤
                  ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - 1 / (16 * ((d : ℝ) + 2)))))) :
      let Q0 : Opens (SpatialCoordinates d) :=
        centeredCube (qc n0)
          (qs n0) (hr n0)
      let mu0 : BilateralField d → Measure (SpatialCoordinates d) :=
        fun omega => (muFull omega).restrict (closure (Q0 : Set (SpatialCoordinates d)))
      let Elim0 : BilateralField d → DomainL2 Q0 → ℝ≥0∞ :=
        fun omega u => (limitFormEnergy (G n0 omega) u).toENNReal
      let Func0 : BilateralField d → ℝ →
          BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          DomainL2 Q0 → ℝ :=
        fun omega lam f u =>
          (Elim0 omega u).toReal +
            lam * (∫ x, J n0 omega u x ^ 2 ∂(mu0 omega)) -
            2 * (∫ x, f x * J n0 omega u x ∂(mu0 omega))
      ∃ Rn : BilateralField d → ℝ →
          BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          SpatialCoordinates d → ℝ,
        (∀ (lam : ℝ), 0 < lam →
          ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
            Measurable (fun p : BilateralField d × SpatialCoordinates d =>
              Rn p.1 lam f p.2)) ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (∀ (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ContinuousOn (Rn omega lam f) (closure (Q0 : Set (SpatialCoordinates d))) ∧
              ∀ x ∈ frontier (Q0 : Set (SpatialCoordinates d)),
                Rn omega lam f x = 0) ∧
          (∀ (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ∀ delta : ℝ, 0 < delta → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
                ∀ x ∈ closure (Q0 : Set (SpatialCoordinates d)),
                  |RN n0 N omega lam f x - Rn omega lam f x| < delta) ∧
          (∀ (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ∃ ustar : DomainL2 Q0,
                Elim0 omega ustar ≠ ⊤ ∧
                (Rn omega lam f) =ᵐ[volume.restrict (Q0 : Set (SpatialCoordinates d))]
                  (ustar : SpatialCoordinates d → ℝ) ∧
                (∀ v : DomainL2 Q0,
                  Elim0 omega v ≠ ⊤ → Func0 omega lam f ustar ≤ Func0 omega lam f v) ∧
                (∀ v : DomainL2 Q0,
                  Elim0 omega v ≠ ⊤ →
                  (∀ w : DomainL2 Q0,
                    Elim0 omega w ≠ ⊤ → Func0 omega lam f v ≤ Func0 omega lam f w) →
                  v = ustar)))  := by
  exact aux_mfd_prop_as_forms_hFixedCube_glue hd Sf Interp M H hHI PN KN hKN hin
    (fun _ : ℕ => qc n0) (fun _ : ℕ => qs n0) (fun _ : ℕ => hr n0)
    (fun _ => hP n0) (fun _ => G n0) (hGtendsto.mono fun omega h _ => h n0) muFull
    (hmuFull.mono fun omega h => ⟨h.1, fun _ => h.2.1 n0, fun _ => h.2.2 n0⟩)
    (fun _ => T n0) (fun _ => Ktrace n0) (fun _ => Ctrace n0)
    (hT.mono fun omega h _ => h n0) (fun _ => i n0) (h_i_val.mono fun omega h _ => h n0)
    (fun _ => J n0) (hJ.mono fun omega h _ => h n0)
    (fun _ => RN n0) (fun _ => hRN_formula n0) 0 hHolder L hL hLlocal
    deltaGrowth hMdeltaGrowth hGrowth_all


/-- Operator-norm convergence implies strong convergence of the actual killed inverse. -/
theorem aux_mfd_prop_as_forms_norm_strong {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    {I : Type*} (qc : I → SpatialCoordinates d) (qs : I → ℝ) (hr : ∀ n, 0 < qs n)
    (G : (n : I) → BilateralField d →
      DomainL2 (centeredCube (qc n) (qs n) (hr n)) →L[ℝ]
        DomainL2 (centeredCube (qc n) (qs n) (hr n)))
    (hnorm : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ n : I,
      Tendsto (fun N => volumeResponseOperator
        (killedResponseSpace (aux_mfd_prop_as_forms_poincare hd (qc n) (qs n) (hr n)))
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc n) (hr n))) atTop (𝓝 (G n omega))) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : I) (f : DomainL2 (centeredCube (qc n) (qs n) (hr n))),
        Tendsto (fun N => (responseSolution
          (killedResponseSpace (aux_mfd_prop_as_forms_poincare hd (qc n) (qs n) (hr n)))
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc n) (hr n))
          ((sobolevVolumeLoad f).comp
            (killedResponseSpace (aux_mfd_prop_as_forms_poincare hd (qc n) (qs n) (hr n))).space.subtypeL)).val.1)
          atTop (𝓝 (G n omega f)) := by
  filter_upwards [hnorm] with omega h n f
  have hpt : Tendsto (fun N => volumeResponseOperator
      (killedResponseSpace (aux_mfd_prop_as_forms_poincare hd (qc n) (qs n) (hr n)))
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (qc n) (hr n)) f)
      atTop (𝓝 (G n omega f)) :=
    ((continuous_id.clm_apply continuous_const).tendsto (G n omega)).comp (h n)
  simpa only [volumeResponseOperator_apply] using hpt

/-- Native chaos regularity on any family of open cubes. -/
theorem aux_mfd_prop_as_forms_mu_properties {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (muFull : BilateralField d → Measure (SpatialCoordinates d))
    {I : Type*} (qc : I → SpatialCoordinates d) (qs : I → ℝ) (hr : ∀ n, 0 < qs n)
    (hreg : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => weightedChaosCutoff M H N omega) (muFull omega) ∧
      IsLocallyFiniteMeasure (muFull omega) ∧
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        muFull omega (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
      (∀ n : I, muFull omega (frontier (centeredCube (qc n) (qs n) (hr n) : Set (SpatialCoordinates d))) = 0) ∧
      (∀ n : I, muFull omega (closure (centeredCube (qc n) (qs n) (hr n) : Set (SpatialCoordinates d))) < ⊤) := by
  filter_upwards [hreg] with omega h
  have heq : (fun N => cutoffSpeedMeasure M H omega N) =
      fun N => weightedChaosCutoff M H N omega :=
    funext fun N => cutoffSpeedMeasure_eq_weightedChaosCutoff M H omega N
  have := h.2.1
  refine ⟨by rw [heq]; exact h.1, fun n => h.2.2 _ _ _, fun n => ?_⟩
  exact (centeredCube_isBounded (qc n) (hr n)).isCompact_closure.measure_lt_top


def aux_mfd_prop_as_forms_GN {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (n : SubdiffusiveProcess.Section9.RationalCubeIndex d) (omega : BilateralField d) (N : ℕ) :
    DomainL2 (SubdiffusiveProcess.Section9.rationalCube d n) →L[ℝ] DomainL2 (SubdiffusiveProcess.Section9.rationalCube d n) :=
  volumeResponseOperator
    (killedResponseSpace (aux_mfd_prop_as_forms_poincare hd
      (SubdiffusiveProcess.Section9.rationalCubeCenter d n) (SubdiffusiveProcess.Section9.rationalCubeSide d n)
      (SubdiffusiveProcess.Section9.rationalCubeSide_pos d n)))
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
      (SubdiffusiveProcess.Section9.rationalCubeCenter d n) (SubdiffusiveProcess.Section9.rationalCubeSide_pos d n))

def aux_mfd_prop_as_forms_EN {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (n : SubdiffusiveProcess.Section9.RationalCubeIndex d) (omega : BilateralField d) (N : ℕ)
    (u : DomainL2 (SubdiffusiveProcess.Section9.rationalCube d n)) : EReal :=
  ⨅ v : {v : killedSobolevGraph (SubdiffusiveProcess.Section9.rationalCube d n) //
      (v : SobolevData (SubdiffusiveProcess.Section9.rationalCube d n)).1 = u},
    ((in_killed_energy M H hH omega N (SubdiffusiveProcess.Section9.rationalCubeCenter d n)
      (SubdiffusiveProcess.Section9.rationalCubeSide_pos d n)
      (v : killedSobolevGraph (SubdiffusiveProcess.Section9.rationalCube d n))
      (v : killedSobolevGraph (SubdiffusiveProcess.Section9.rationalCube d n)) : ℝ) : EReal)

def aux_mfd_prop_as_forms_RN {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (n : SubdiffusiveProcess.Section9.RationalCubeIndex d) (N : ℕ) (omega : BilateralField d) (lam : ℝ)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d) : ℝ :=
  ∫ path, (∫ t in Set.Ioi (0 : ℝ),
    Set.indicator {s : ℝ | ENNReal.ofReal s <
      ContinuousPath.exitTime (SubdiffusiveProcess.Section9.rationalCube d n : Set (SpatialCoordinates d)) path}
      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) ∂(KN N (omega, x))


theorem aux_mfd_prop_as_forms_after_inverse
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Interp : CubeFractionalInterpolationInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHI : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : in_crossing M H PN KN)
    (_hinput : aux_cutoff_lifetime_package_LocalInput M H KN)
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ N omega x, Measure.map LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega))
    (hHolderModel : ∀ (qc : ℕ → SpatialCoordinates d) (qs : ℕ → ℝ)
        (hr : ∀ n : ℕ, 0 < qs n)
        (_htri : ∀ n : ℕ, ∃ j : ℤ, qs n = (3 : ℝ) ^ j)
        (RN : ℕ → ℕ → BilateralField d → ℝ →
            BoundedContinuousFunction (SpatialCoordinates d) ℝ →
            SpatialCoordinates d → ℝ)
        (_hRN_formula : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
            (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
            (x : SpatialCoordinates d),
          RN n N omega lam f x =
            ∫ path, (∫ t in Set.Ioi (0 : ℝ),
              Set.indicator
                {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                  (centeredCube (qc n)
                    (qs n) (hr n) : Set (SpatialCoordinates d)) path}
                (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
              ∂(KN N (omega, x)))
        (n0 : ℕ),
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        (∃ K1 : ℝ, 0 < K1 ∧ ∀ (N : ℕ)
          (v : killedSobolevGraph (centeredCube (qc n0) (qs n0) (hr n0))),
          cubeFractionalSqNorm hd (qc n0) (qs n0) (hr n0) threeQuarterOrder v.val.1 ≤
            K1 * sobolevCoefficientForm
              (cutoffPositiveCoefficient M H omega N (qc n0) (hr n0)) v.val v.val) ∧
        ∀ (lam0 lam1 : ℝ), 0 < lam0 → lam0 ≤ lam1 →
          ∃ Kom : ℝ, 0 < Kom ∧ ∀ (N : ℕ) (lam : ℝ), lam0 ≤ lam → lam ≤ lam1 →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ‖f‖ ≤ 1 →
              (∀ x ∈ closure (centeredCube (qc n0)
                  (qs n0) (hr n0) : Set (SpatialCoordinates d)),
                |RN n0 N omega lam f x| ≤ Kom) ∧
              ∀ x ∈ closure (centeredCube (qc n0)
                  (qs n0) (hr n0) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure (centeredCube (qc n0)
                  (qs n0) (hr n0) : Set (SpatialCoordinates d)),
                |RN n0 N omega lam f x - RN n0 N omega lam f y| ≤
                  Kom * dist x y ^ (1 / 4 : ℝ))
    (deltaGrowth : ℝ) (hMdeltaGrowth : M.delta ≤ deltaGrowth)
    (hGrowth_all : ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ deltaGrowth →
      ∃ mu : BilateralField d → Measure (SpatialCoordinates d),
        Measurable mu ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          MeasuresConvergeLocally (fun N ↦ weightedChaosCutoff M H N omega) (mu omega) ∧
          IsLocallyFiniteMeasure (mu omega) ∧
          (mu omega).IsOpenPosMeasure ∧ NullSingletonClass (mu omega) ∧
          (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
            mu omega (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0)) ∧
        ∀ (R : Set (SpatialCoordinates d)), Bornology.IsBounded R →
          ∃ Kmu : BilateralField d → ℝ,
            MemLp Kmu (↑(16 * d * (d + 2) + 1) : ℝ≥0∞) (chaosSampleLaw M).toMeasure ∧
            ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              0 ≤ Kmu omega ∧
              (∀ N x, x ∈ R → ∀ r, 0 < r → r ≤ 1 →
                weightedChaosCutoff M H N omega (Metric.ball x r) ≤
                  ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - 1 / (16 * ((d : ℝ) + 2))))) ∧
              (∀ x, x ∈ R → ∀ r, 0 < r → r ≤ 1 →
                mu omega (Metric.ball x r) ≤
                  ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - 1 / (16 * ((d : ℝ) + 2)))))) :
        ∀ (G : (n : (SubdiffusiveProcess.Section9.RationalCubeIndex d)) → BilateralField d →
            (DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n) →L[ℝ] DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n))),
        (∀ n, Measurable (G n)) →
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ n : (SubdiffusiveProcess.Section9.RationalCubeIndex d),
          Tendsto ((aux_mfd_prop_as_forms_GN hd M H) n omega) atTop (𝓝 (G n omega)) ∧ IsCompactOperator (G n omega) ∧
          (∀ x y : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n), inner ℝ (G n omega x) y = inner ℝ x (G n omega y)) ∧
          (∀ x : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n), 0 ≤ inner ℝ x (G n omega x)) ∧ Function.Injective (G n omega) ∧
          (∃ F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (((SubdiffusiveProcess.Section9.rationalCube d) n) : Set (SpatialCoordinates d))),
            (∀ u : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n), F.toClosedForm.energy u = limitFormEnergy (G n omega) u) ∧
            _root_.SubdiffusiveProcess.DirichletForm.IsRegular F.toClosedForm ∧ _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal F.toClosedForm) ∧
          (∀ (uN : ℕ → DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n)) (u : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n)),
            (∀ f : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n), Tendsto (fun N => inner ℝ f (uN N)) atTop (𝓝 (inner ℝ f u))) →
            limitFormEnergy (G n omega) u ≤ liminf (fun N => (aux_mfd_prop_as_forms_EN M H hHI) n omega N (uN N)) atTop) ∧
          (∀ u : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n), ∃ w : ℕ → DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n), Tendsto w atTop (𝓝 u) ∧
            limsup (fun N => (aux_mfd_prop_as_forms_EN M H hHI) n omega N (w N)) atTop ≤ limitFormEnergy (G n omega) u) ∧
          (∀ u : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n), limitFormEnergy (G n omega) u ≠ ⊤ →
            ∃ v : CubeFractionalL2 (k := 1) hd ((SubdiffusiveProcess.Section9.rationalCubeCenter d) n) ((SubdiffusiveProcess.Section9.rationalCubeSide d) n) ((SubdiffusiveProcess.Section9.rationalCubeSide_pos d) n) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder, v.val 0 = u)) →
        ∃ (muFull : BilateralField d → Measure (SpatialCoordinates d))
          (Rlim : (SubdiffusiveProcess.Section9.RationalCubeIndex d) → BilateralField d → ℝ →
            BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ),
          (∀ n, Measurable (G n)) ∧ Measurable muFull ∧
          (∀ (n : (SubdiffusiveProcess.Section9.RationalCubeIndex d)) (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              Measurable (fun p : BilateralField d × SpatialCoordinates d =>
                Rlim n p.1 lam f p.2)) ∧
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
            (∀ n, muFull omega (frontier ((SubdiffusiveProcess.Section9.rationalCube d) n : Set (SpatialCoordinates d))) = 0) ∧
            (∀ n, muFull omega (closure ((SubdiffusiveProcess.Section9.rationalCube d) n : Set (SpatialCoordinates d))) < ⊤) ∧
            ∀ n : (SubdiffusiveProcess.Section9.RationalCubeIndex d),
              Tendsto ((aux_mfd_prop_as_forms_GN hd M H) n omega) atTop (𝓝 (G n omega)) ∧
              (∀ G' : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n) →L[ℝ] DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n),
                Tendsto ((aux_mfd_prop_as_forms_GN hd M H) n omega) atTop (𝓝 G') → G' = G n omega) ∧
              IsCompactOperator (G n omega) ∧
              (∀ x y : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n),
                inner ℝ (G n omega x) y = inner ℝ x (G n omega y)) ∧
              (∀ x : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n), 0 ≤ inner ℝ x (G n omega x)) ∧
              Function.Injective (G n omega) ∧
              (∃ F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict ((SubdiffusiveProcess.Section9.rationalCube d) n : Set (SpatialCoordinates d))),
                (∀ u : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n), F.toClosedForm.energy u = limitFormEnergy (G n omega) u) ∧
                _root_.SubdiffusiveProcess.DirichletForm.IsRegular F.toClosedForm ∧
                _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal F.toClosedForm) ∧
              (∀ (uN : ℕ → DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n)) (u : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n)),
                (∀ f : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n),
                  Tendsto (fun N => inner ℝ f (uN N)) atTop (𝓝 (inner ℝ f u))) →
                limitFormEnergy (G n omega) u ≤ liminf (fun N => (aux_mfd_prop_as_forms_EN M H hHI) n omega N (uN N)) atTop) ∧
              (∀ u : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n), ∃ w : ℕ → DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n),
                Tendsto w atTop (𝓝 u) ∧
                limsup (fun N => (aux_mfd_prop_as_forms_EN M H hHI) n omega N (w N)) atTop ≤ limitFormEnergy (G n omega) u) ∧
              (∀ (lam : ℝ), 0 < lam →
                ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
                  ContinuousOn (Rlim n omega lam f) (closure ((SubdiffusiveProcess.Section9.rationalCube d) n : Set (SpatialCoordinates d))) ∧
                  (∀ x ∈ frontier ((SubdiffusiveProcess.Section9.rationalCube d) n : Set (SpatialCoordinates d)), Rlim n omega lam f x = 0) ∧
                  ∀ eps : ℝ, 0 < eps → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
                    ∀ x ∈ closure ((SubdiffusiveProcess.Section9.rationalCube d) n : Set (SpatialCoordinates d)),
                      |(aux_mfd_prop_as_forms_RN KN) n N omega lam f x - Rlim n omega lam f x| < eps) ∧
              (∀ (lam0 lam1 : ℝ), 0 < lam0 → lam0 ≤ lam1 →
                ∃ Kom : ℝ, 0 < Kom ∧ ∀ (N : ℕ) (lam : ℝ), lam0 ≤ lam → lam ≤ lam1 →
                  ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ‖f‖ ≤ 1 →
                    (∀ x ∈ closure ((SubdiffusiveProcess.Section9.rationalCube d) n : Set (SpatialCoordinates d)), |(aux_mfd_prop_as_forms_RN KN) n N omega lam f x| ≤ Kom) ∧
                    ∀ x ∈ closure ((SubdiffusiveProcess.Section9.rationalCube d) n : Set (SpatialCoordinates d)),
                      ∀ y ∈ closure ((SubdiffusiveProcess.Section9.rationalCube d) n : Set (SpatialCoordinates d)),
                        |(aux_mfd_prop_as_forms_RN KN) n N omega lam f x - (aux_mfd_prop_as_forms_RN KN) n N omega lam f y| ≤
                          Kom * dist x y ^ (1 / 4 : ℝ)) ∧
              (let mu := (muFull omega).restrict (closure ((SubdiffusiveProcess.Section9.rationalCube d) n : Set (SpatialCoordinates d)));
               ∃ (T : CubeFractionalL2 (k := 1) hd ((SubdiffusiveProcess.Section9.rationalCubeCenter d) n)
                   ((SubdiffusiveProcess.Section9.rationalCubeSide d) n) ((SubdiffusiveProcess.Section9.rationalCubeSide_pos d) n) halfFractionalOrder → Lp ℝ 2 mu)
                 (Ktrace Ctrace : ℝ),
                 0 ≤ Ktrace ∧ 0 ≤ Ctrace ∧
                 (∀ u v : CubeFractionalL2 (k := 1) hd ((SubdiffusiveProcess.Section9.rationalCubeCenter d) n) ((SubdiffusiveProcess.Section9.rationalCubeSide d) n) ((SubdiffusiveProcess.Section9.rationalCubeSide_pos d) n) halfFractionalOrder,
                   ∃ w : CubeFractionalL2 (k := 1) hd ((SubdiffusiveProcess.Section9.rationalCubeCenter d) n) ((SubdiffusiveProcess.Section9.rationalCubeSide d) n) ((SubdiffusiveProcess.Section9.rationalCubeSide_pos d) n) halfFractionalOrder,
                     w.val 0 = u.val 0 - v.val 0) ∧
                 (∀ u v w : CubeFractionalL2 (k := 1) hd ((SubdiffusiveProcess.Section9.rationalCubeCenter d) n) ((SubdiffusiveProcess.Section9.rationalCubeSide d) n) ((SubdiffusiveProcess.Section9.rationalCubeSide_pos d) n) halfFractionalOrder,
                   w.val 0 = u.val 0 - v.val 0 →
                   ‖T u - T v‖ ^ 2 ≤
                     Ctrace * (Ktrace + (mu (closure ((SubdiffusiveProcess.Section9.rationalCube d) n : Set (SpatialCoordinates d)))).toReal) *
                       (cubeFractionalL2Norm hd ((SubdiffusiveProcess.Section9.rationalCubeCenter d) n) ((SubdiffusiveProcess.Section9.rationalCubeSide d) n) ((SubdiffusiveProcess.Section9.rationalCubeSide_pos d) n) halfFractionalOrder w) ^ 2) ∧
                 (∀ f : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ f →
                   ∀ v : CubeFractionalL2 (k := 1) hd ((SubdiffusiveProcess.Section9.rationalCubeCenter d) n) ((SubdiffusiveProcess.Section9.rationalCubeSide d) n) ((SubdiffusiveProcess.Section9.rationalCubeSide_pos d) n) halfFractionalOrder,
                     (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
                       volume.restrict ((SubdiffusiveProcess.Section9.rationalCube d) n : Set (SpatialCoordinates d))] f →
                     ∀ hf : MemLp f 2 mu, T v = hf.toLp f) ∧
                 ∃ J : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n) → Lp ℝ 2 mu,
                   (∀ u : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n), (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤ →
                     ∃ v : CubeFractionalL2 (k := 1) hd ((SubdiffusiveProcess.Section9.rationalCubeCenter d) n)
                         ((SubdiffusiveProcess.Section9.rationalCubeSide d) n) ((SubdiffusiveProcess.Section9.rationalCubeSide_pos d) n) halfFractionalOrder,
                       v.val 0 = u ∧ T v = J u) ∧
                   ∀ (lam : ℝ), 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
                     let Func : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n) → ℝ := fun u =>
                       (limitFormEnergy (G n omega) u).toENNReal.toReal +
                       lam * (∫ x, (J u x) ^ 2 ∂mu) - 2 * (∫ x, f x * J u x ∂mu);
                     ∃ ustar : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n),
                       (limitFormEnergy (G n omega) ustar).toENNReal ≠ ⊤ ∧
                       (Rlim n omega lam f) =ᵐ[volume.restrict ((SubdiffusiveProcess.Section9.rationalCube d) n : Set (SpatialCoordinates d))]
                         (ustar : SpatialCoordinates d → ℝ) ∧
                       (∀ v : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n), (limitFormEnergy (G n omega) v).toENNReal ≠ ⊤ →
                         Func ustar ≤ Func v) ∧
                       (∀ v : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n), (limitFormEnergy (G n omega) v).toENNReal ≠ ⊤ →
                         (∀ w : DomainL2 ((SubdiffusiveProcess.Section9.rationalCube d) n), (limitFormEnergy (G n omega) w).toENNReal ≠ ⊤ →
                           Func v ≤ Func w) → v = ustar))) := by
  classical
  intro G hGmeas hGAll
  let I := SubdiffusiveProcess.Section9.RationalCubeIndex d
  let cz : I → SpatialCoordinates d := SubdiffusiveProcess.Section9.rationalCubeCenter d
  let r : I → ℝ := SubdiffusiveProcess.Section9.rationalCubeSide d
  let hr : ∀ n : I, 0 < r n := SubdiffusiveProcess.Section9.rationalCubeSide_pos d
  let Qn : I → Opens (SpatialCoordinates d) := SubdiffusiveProcess.Section9.rationalCube d
  let RN := aux_mfd_prop_as_forms_RN KN
  have hGstrong := aux_mfd_prop_as_forms_norm_strong hd M H cz r hr G
    (hGAll.mono fun omega h n => (h n).1)
  obtain ⟨muFull, hMuMeas, hMuReg, hMuGrowth⟩ := hGrowth_all M H hHI hMdeltaGrowth
  have hMu := aux_mfd_prop_as_forms_mu_properties M H muFull cz r hr
    (hMuReg.mono fun omega h => ⟨h.1, h.2.1, h.2.2.2.2⟩)
  have hTr : ∀ n : I,
      ∃ (T : (omega : BilateralField d) →
          CubeFractionalL2 (k := 1) hd (cz n) (r n) (hr n) halfFractionalOrder →
            Lp ℝ 2 ((muFull omega).restrict (closure (Qn n : Set (SpatialCoordinates d)))))
        (K C : BilateralField d → ℝ),
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, 0 ≤ K omega ∧ 0 ≤ C omega ∧
          SubdiffusiveProcess.Section9.CubeTraceCharacterization hd (cz n) (hr n)
            ((muFull omega).restrict (closure (Qn n : Set (SpatialCoordinates d))))
            (K omega) (C omega) (T omega) := by
    intro n
    apply aux_mfd_prop_as_forms_trace_supply hd M (cz n) (r n) (hr n) muFull
      (hMu.mono fun omega h => h.2.2 n)
    obtain ⟨K, _hKLp, hK⟩ := hMuGrowth
      (closure (Qn n : Set (SpatialCoordinates d)))
      (centeredCube_isBounded (cz n) (hr n)).closure
    exact ⟨K, hK.mono fun _ h => ⟨h.1, h.2.2⟩⟩
  choose T Ktrace Ctrace hT using hTr
  have hTAll := ae_all_iff.2 hT
  obtain ⟨i, hi⟩ := aux_mfd_prop_as_forms_lift_supply hd M cz r hr G
    (hGAll.mono fun omega h n => (h n).2.2.2.2.2.2.2.2)
  let J : (n : I) → (omega : BilateralField d) → DomainL2 (Qn n) →
      Lp ℝ 2 ((muFull omega).restrict (closure (Qn n : Set (SpatialCoordinates d)))) :=
    fun n omega u => if hu : (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤ then
      T n omega (i n omega u hu) else 0
  have hJ : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : I) (u : DomainL2 (Qn n)) (hu : (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤),
        J n omega u = T n omega (i n omega u hu) := by
    exact Eventually.of_forall fun omega n u hu => by simp only [J, dite_eq_left hu]
  have hHol := fun n : I => hHolderModel
    (fun _ : ℕ => cz n) (fun _ : ℕ => r n) (fun _ : ℕ => hr n)
    (fun _ => ⟨n.2, rfl⟩) (fun _ => RN n) (fun _ _ _ _ _ _ => rfl) 0
  have hHolAll := ae_all_iff.2 hHol
  have hR := fun n : I => aux_mfd_prop_as_forms_cube_glue_call hd Sf Interp M H hHI PN KN hKN hin
    cz r hr (fun n => aux_mfd_prop_as_forms_poincare hd (cz n) (r n) (hr n))
    G hGstrong muFull hMu T Ktrace Ctrace hTAll i hi
    (fun n omega u => (J n omega u : SpatialCoordinates d → ℝ))
    (hJ.mono fun omega h n u hu =>
      Filter.EventuallyEq.of_eq (congrArg
        (fun v : Lp ℝ 2 ((muFull omega).restrict (closure (Qn n : Set (SpatialCoordinates d)))) =>
          (v : SpatialCoordinates d → ℝ)) (h n u hu)))
    RN (fun _ _ _ _ _ _ => rfl) n (hHol n) L hL hLlocal deltaGrowth hMdeltaGrowth hGrowth_all
  choose Rlim hRmeas hRae using hR
  refine ⟨muFull, Rlim, hGmeas, hMuMeas, hRmeas, ?_⟩
  filter_upwards [hMu, hGAll, hTAll, hi, hJ, hHolAll, ae_all_iff.2 hRae] with
    omega hm hg ht hiω hj hh hrω
  refine ⟨hm.1, hm.2.1, hm.2.2, ?_⟩
  intro n
  obtain ⟨hgn, hcompact, hsym, hpos, hinj, hform, hlo, hup, _hco⟩ := hg n
  refine ⟨hgn, fun G' hG' => tendsto_nhds_unique hG' hgn,
    hcompact, hsym, hpos, hinj, hform, hlo, hup, ?_, (hh n).2, ?_⟩
  · intro lam hlam f
    exact ⟨((hrω n).1 lam hlam f).1, ((hrω n).1 lam hlam f).2,
      (hrω n).2.1 lam hlam f⟩
  · refine ⟨T n omega, Ktrace n omega, Ctrace n omega,
      (ht n).1, (ht n).2.1, (ht n).2.2.1, (ht n).2.2.2.1,
      (ht n).2.2.2.2, J n omega, ?_, (hrω n).2.2⟩
    intro u hu
    exact ⟨i n omega u hu, hiω n u hu, (hj n u hu).symm⟩


/-- A1. One native-model threshold and one common event for norm/Mosco/resolvent
convergence and uniform finite-cutoff Holder bounds. The inverse G occurring in
all clauses is the same, and the resolvent is characterized by its actual
speed-measure variational functional. All analytic and process suppliers are
outputs or proof obligations, with no carried result/input bundle. -/
theorem mfd_prop_as_forms
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
      ∃ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization M H)
        (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hKN : ∀ N, IsMarkovKernel (KN N)),
        in_crossing M H PN KN ∧
        (let I := (Fin d → ℚ) × ℤ;
        let cz : I → SpatialCoordinates d := fun n i => (n.1 i : ℝ);
        let r : I → ℝ := fun n => (3 : ℝ) ^ n.2;
        let hr : ∀ n, 0 < r n := fun n => zpow_pos (by norm_num) n.2;
        let Qn : I → Opens (SpatialCoordinates d) := fun n =>
          centeredCube (cz n)
            (r n) (hr n);
        let GN : (n : I) → BilateralField d → ℕ →
            (DomainL2 (Qn n) →L[ℝ] DomainL2 (Qn n)) := fun n omega N =>
          volumeResponseOperator
            (killedResponseSpace (aux_mfd_prop_as_forms_poincare hd
              (cz n)
              (r n) (hr n)))
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
              (cz n) (hr n));
        let EN : (n : I) → BilateralField d → ℕ → DomainL2 (Qn n) → EReal :=
          fun n omega N u =>
            ⨅ v : {v : killedSobolevGraph (Qn n) //
                (v : SobolevData (Qn n)).1 = u},
              ((in_killed_energy M H hH omega N (cz n)
                (hr n) (v : killedSobolevGraph (Qn n))
                (v : killedSobolevGraph (Qn n)) : ℝ) : EReal);
        let RN : I → ℕ → BilateralField d → ℝ →
            BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ :=
          fun n N omega lam f x =>
            ∫ path, (∫ t in Set.Ioi (0 : ℝ),
              Set.indicator {s : ℝ | ENNReal.ofReal s <
                ContinuousPath.exitTime (Qn n : Set (SpatialCoordinates d)) path}
                (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
              ∂(KN N (omega, x));
        ∃ (G : (n : I) → BilateralField d →
            (DomainL2 (Qn n) →L[ℝ] DomainL2 (Qn n)))
          (muFull : BilateralField d → Measure (SpatialCoordinates d))
          (Rlim : I → BilateralField d → ℝ →
            BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ),
          (∀ n, Measurable (G n)) ∧ Measurable muFull ∧
          (∀ (n : I) (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              Measurable (fun p : BilateralField d × SpatialCoordinates d =>
                Rlim n p.1 lam f p.2)) ∧
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
            (∀ n, muFull omega (frontier (Qn n : Set (SpatialCoordinates d))) = 0) ∧
            (∀ n, muFull omega (closure (Qn n : Set (SpatialCoordinates d))) < ⊤) ∧
            ∀ n : I,
              Tendsto (GN n omega) atTop (𝓝 (G n omega)) ∧
              (∀ G' : DomainL2 (Qn n) →L[ℝ] DomainL2 (Qn n),
                Tendsto (GN n omega) atTop (𝓝 G') → G' = G n omega) ∧
              IsCompactOperator (G n omega) ∧
              (∀ x y : DomainL2 (Qn n),
                inner ℝ (G n omega x) y = inner ℝ x (G n omega y)) ∧
              (∀ x : DomainL2 (Qn n), 0 ≤ inner ℝ x (G n omega x)) ∧
              Function.Injective (G n omega) ∧
              (∃ F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Qn n : Set (SpatialCoordinates d))),
                (∀ u : DomainL2 (Qn n), F.toClosedForm.energy u = limitFormEnergy (G n omega) u) ∧
                _root_.SubdiffusiveProcess.DirichletForm.IsRegular F.toClosedForm ∧
                _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal F.toClosedForm) ∧
              (∀ (uN : ℕ → DomainL2 (Qn n)) (u : DomainL2 (Qn n)),
                (∀ f : DomainL2 (Qn n),
                  Tendsto (fun N => inner ℝ f (uN N)) atTop (𝓝 (inner ℝ f u))) →
                limitFormEnergy (G n omega) u ≤ liminf (fun N => EN n omega N (uN N)) atTop) ∧
              (∀ u : DomainL2 (Qn n), ∃ w : ℕ → DomainL2 (Qn n),
                Tendsto w atTop (𝓝 u) ∧
                limsup (fun N => EN n omega N (w N)) atTop ≤ limitFormEnergy (G n omega) u) ∧
              (∀ (lam : ℝ), 0 < lam →
                ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
                  ContinuousOn (Rlim n omega lam f) (closure (Qn n : Set (SpatialCoordinates d))) ∧
                  (∀ x ∈ frontier (Qn n : Set (SpatialCoordinates d)), Rlim n omega lam f x = 0) ∧
                  ∀ eps : ℝ, 0 < eps → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
                    ∀ x ∈ closure (Qn n : Set (SpatialCoordinates d)),
                      |RN n N omega lam f x - Rlim n omega lam f x| < eps) ∧
              (∀ (lam0 lam1 : ℝ), 0 < lam0 → lam0 ≤ lam1 →
                ∃ Kom : ℝ, 0 < Kom ∧ ∀ (N : ℕ) (lam : ℝ), lam0 ≤ lam → lam ≤ lam1 →
                  ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ‖f‖ ≤ 1 →
                    (∀ x ∈ closure (Qn n : Set (SpatialCoordinates d)), |RN n N omega lam f x| ≤ Kom) ∧
                    ∀ x ∈ closure (Qn n : Set (SpatialCoordinates d)),
                      ∀ y ∈ closure (Qn n : Set (SpatialCoordinates d)),
                        |RN n N omega lam f x - RN n N omega lam f y| ≤
                          Kom * dist x y ^ (1 / 4 : ℝ)) ∧
              (let mu := (muFull omega).restrict (closure (Qn n : Set (SpatialCoordinates d)));
               ∃ (T : CubeFractionalL2 (k := 1) hd (cz n)
                   (r n) (hr n) halfFractionalOrder → Lp ℝ 2 mu)
                 (Ktrace Ctrace : ℝ),
                 0 ≤ Ktrace ∧ 0 ≤ Ctrace ∧
                 (∀ u v : CubeFractionalL2 (k := 1) hd (cz n) (r n) (hr n) halfFractionalOrder,
                   ∃ w : CubeFractionalL2 (k := 1) hd (cz n) (r n) (hr n) halfFractionalOrder,
                     w.val 0 = u.val 0 - v.val 0) ∧
                 (∀ u v w : CubeFractionalL2 (k := 1) hd (cz n) (r n) (hr n) halfFractionalOrder,
                   w.val 0 = u.val 0 - v.val 0 →
                   ‖T u - T v‖ ^ 2 ≤
                     Ctrace * (Ktrace + (mu (closure (Qn n : Set (SpatialCoordinates d)))).toReal) *
                       (cubeFractionalL2Norm hd (cz n) (r n) (hr n) halfFractionalOrder w) ^ 2) ∧
                 (∀ f : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ f →
                   ∀ v : CubeFractionalL2 (k := 1) hd (cz n) (r n) (hr n) halfFractionalOrder,
                     (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
                       volume.restrict (Qn n : Set (SpatialCoordinates d))] f →
                     ∀ hf : MemLp f 2 mu, T v = hf.toLp f) ∧
                 ∃ J : DomainL2 (Qn n) → Lp ℝ 2 mu,
                   (∀ u : DomainL2 (Qn n), (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤ →
                     ∃ v : CubeFractionalL2 (k := 1) hd (cz n)
                         (r n) (hr n) halfFractionalOrder,
                       v.val 0 = u ∧ T v = J u) ∧
                   ∀ (lam : ℝ), 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
                     let Func : DomainL2 (Qn n) → ℝ := fun u =>
                       (limitFormEnergy (G n omega) u).toENNReal.toReal +
                       lam * (∫ x, (J u x) ^ 2 ∂mu) - 2 * (∫ x, f x * J u x ∂mu);
                     ∃ ustar : DomainL2 (Qn n),
                       (limitFormEnergy (G n omega) ustar).toENNReal ≠ ⊤ ∧
                       (Rlim n omega lam f) =ᵐ[volume.restrict (Qn n : Set (SpatialCoordinates d))]
                         (ustar : SpatialCoordinates d → ℝ) ∧
                       (∀ v : DomainL2 (Qn n), (limitFormEnergy (G n omega) v).toENNReal ≠ ⊤ →
                         Func ustar ≤ Func v) ∧
                       (∀ v : DomainL2 (Qn n), (limitFormEnergy (G n omega) v).toENNReal ≠ ⊤ →
                         (∀ w : DomainL2 (Qn n), (limitFormEnergy (G n omega) w).toENNReal ≠ ⊤ →
                           Func v ≤ Func w) → v = ustar)))) := by
  classical
  obtain ⟨Jc, Pc, Xc, Sf, W, Cp, D, hES, Step, Dbase, Interp, BD, BDQ,
    hcontract, hlife, _EM, δr, Cresp, hδr, _hCresp, hsup⟩ := inputs_simultaneous d hd
  obtain ⟨δg, hδg, hInverse⟩ := aux_mfd_prop_as_forms_inverse_supply d hd Jc Pc Xc Sf W Cp D
    hES Step Dbase Interp BD BDQ hcontract
  obtain ⟨δh, hδh, hHolderSupply⟩ := aux_mfd_prop_as_forms_holder_supply hd Jc Pc Xc Sf W Cp D
    Interp Step Dbase
  obtain ⟨δf, hδf, hFinite⟩ := finiteDimensional_cutoff (d := d) hd
  obtain ⟨δμ, hδμ, hGrowth⟩ := prop_chaos_growth (d := d) hd
    (aux_mfd_convergence_eps d) (aux_mfd_convergence_eps_unit d)
    (aux_mfd_convergence_p d) (aux_mfd_convergence_p_spec d)
  refine ⟨min δr (min δg (min δh (min δf δμ))),
    lt_min hδr (lt_min hδg (lt_min hδh (lt_min hδf hδμ))), ?_⟩
  intro M hM
  have hMr := hM.trans (min_le_left _ _)
  have hMg := hM.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMh := hM.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hMf := hM.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hMμ := hM.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨Rm, Sreg, _hRm, ⟨It⟩⟩ := hsup M M.shellPrefix.delta_pos hMr
  obtain ⟨H, hH⟩ := exists_infraredCharacterization hd M
  obtain ⟨PN, KN, hKN, hin, hinput⟩ := hlife M H hH (hFinite M H hH hMf)
  obtain ⟨L, hL, hLlocal, _hLstrong⟩ := aux_cutoff_lifetime_package_local M H KN hinput
  refine ⟨H, hH, PN, KN, hKN, hin, ?_⟩
  dsimp only
  let I := SubdiffusiveProcess.Section9.RationalCubeIndex d
  let cz : I → SpatialCoordinates d := SubdiffusiveProcess.Section9.rationalCubeCenter d
  let r : I → ℝ := SubdiffusiveProcess.Section9.rationalCubeSide d
  let hr : ∀ n : I, 0 < r n := SubdiffusiveProcess.Section9.rationalCubeSide_pos d
  have hGex := fun n : I => hInverse M Rm Sreg It H hH hMg (cz n) (r n) (hr n)
    ⟨n.2, rfl⟩ (fun k => ⟨n.1 k, rfl⟩)
  choose G hGmeas hGae using hGex
  have hGAll := ae_all_iff.2 hGae
  have hpEq : aux_mfd_convergence_p d = 16 * d * (d + 2) + 1 := by
    unfold aux_mfd_convergence_p
    ring
  refine ⟨G, ?_⟩
  exact aux_mfd_prop_as_forms_after_inverse hd Sf Interp M H hH PN KN hKN hin hinput
    L hL hLlocal (hHolderSupply M Rm Sreg It hMh H hH PN KN hKN hin hinput)
    δμ hMμ (by simpa only [aux_mfd_convergence_eps, hpEq] using! hGrowth) G hGmeas hGAll

end SubdiffusiveProcess.Paper
