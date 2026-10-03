module

public import SubdiffusiveProcess.Paper.finite_speed_resolvent_killed_bridge
public import SubdiffusiveProcess.Paper.cutoff_lifetime_package
public import SubdiffusiveProcess.Paper.prop_limit_properties_cutoff_symmetry
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.in_killed_energy
public import SubdiffusiveProcess.Paper.killed_generator_normalization
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffSpeedMeasure
public import SubdiffusiveProcess.Lane4.Carriers
public import MarkovProcess.Path.ExitTime
public import MarkovProcess.Killed.Resolvent

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

namespace Paper




private theorem aux_finite_speed_resolvent_properties_ibp
    {d : Nat} (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : Nat)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hC : ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (hρ : ∀ x : SpatialCoordinates d,
      cutoffSpeedDensity M H omega N x =
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * cutoffCoefficient M H omega N x) :
    ∀ phi psi : SpatialCoordinates d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) phi → ContDiff ℝ (⊤ : ℕ∞) psi →
      HasCompactSupport phi → HasCompactSupport psi →
      Function.support phi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      Function.support psi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      -(∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ((cutoffSpeedDensity M H omega N x)⁻¹ *
          ∑ i : Fin d,
            (fderiv ℝ (fun y => cutoffCoefficient M H omega N y *
              (fderiv ℝ phi y) (Pi.single i 1)) x) (Pi.single i 1)) * psi x
          ∂(cutoffSpeedMeasure M H omega N)) =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          cutoffCoefficient M H omega N x *
            (∑ i : Fin d,
              (fderiv ℝ phi x) (Pi.single i 1) *
                (fderiv ℝ psi x) (Pi.single i 1)) := by
  intro phi psi hphi hpsi hphi_compact hpsi_compact hphi_support hpsi_support
  let Q : Set (SpatialCoordinates d) := centeredCube z r hr
  let A : SpatialCoordinates d → ℝ := cutoffCoefficient M H omega N
  let rho : SpatialCoordinates d → ℝ := cutoffSpeedDensity M H omega N
  have hAcont : Continuous A := by
    dsimp [A, cutoffCoefficient]
    refine continuous_const.mul (Real.continuous_exp.comp ?_)
    unfold cutoffPotential
    fun_prop
  have hρpos : ∀ x, 0 < rho x := by
    intro x
    dsimp [rho, cutoffSpeedDensity]
    exact Real.exp_pos _
  have hρmeas : Measurable (fun x => ENNReal.ofReal (rho x)) := by
    have hρcont : Continuous rho := by
      dsimp [rho, cutoffSpeedDensity]
      have hpot : Continuous (cutoffPotential H omega N) := by
        unfold cutoffPotential
        fun_prop
      exact Real.continuous_exp.comp (hpot.sub continuous_const)
    exact hρcont.measurable.ennreal_ofReal
  have hψ_support' : Function.support psi ⊆ Metric.ball z (r / 2) := by
    simpa [Q, centeredCube] using hpsi_support
  have hψ_tsupport : tsupport psi ⊆ Metric.closedBall z (r / 2) := by
    refine closure_minimal (hψ_support'.trans Metric.ball_subset_closedBall) ?_
    exact Metric.isClosed_closedBall
  have hsphere : volume (Metric.sphere z (r / 2)) = 0 := by
    exact Measure.addHaar_sphere_of_ne_zero volume z (by linarith)
  have hderiv_ae (i : Fin d) :
      ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
        x ∉ Q → (fderiv ℝ psi x) (Pi.single i 1) = 0 := by
    rw [ae_iff]
    apply measure_mono_null ?_ hsphere
    intro x hx
    have hxQ : x ∉ Q := by
      intro hxmem
      apply hx
      intro hxnot
      exact (hxnot hxmem).elim
    have hxder : (fderiv ℝ psi x) (Pi.single i 1) ≠ 0 := by
      intro hz
      apply hx
      intro _
      exact hz
    have hxclosed : x ∈ Metric.closedBall z (r / 2) := by
      by_contra hxc
      apply hxder
      have hzero := fderiv_of_notMem_tsupport ℝ (f := psi) (x := x)
      exact congrArg (fun T => T (Pi.single i 1))
        (hzero (fun hxt => hxc (hψ_tsupport hxt)))
    have hle : dist x z ≤ r / 2 := Metric.mem_closedBall.mp hxclosed
    have hnotlt : ¬ dist x z < r / 2 := by
      intro hlt
      exact hxQ (Metric.mem_ball.mpr hlt)
    exact Metric.mem_sphere.mpr (le_antisymm hle (le_of_not_gt hnotlt))
  have hpsi_zero (x : SpatialCoordinates d) (hx : x ∉ Q) : psi x = 0 := by
    by_contra hpx
    exact hx (hpsi_support (Function.mem_support.mpr hpx))
  have hAi (i : Fin d) :
      ContDiff ℝ 1 (fun x => A x * (fderiv ℝ phi x) (Pi.single i 1)) := by
    have hphid : ContDiff ℝ 1
        (fun x => (fderiv ℝ phi x) (Pi.single i 1)) := by
      have hp : ContDiff ℝ 1
          (fun p : (SpatialCoordinates d) × (SpatialCoordinates d) =>
            (fderiv ℝ phi p.1) p.2) :=
        hphi.contDiff_fderiv_apply (by norm_cast)
      have hc : ContDiff ℝ 1
          (fun x : SpatialCoordinates d =>
            (x, (Pi.single i (1 : ℝ) : SpatialCoordinates d))) :=
        by fun_prop
      simpa only [Function.comp_def] using! hp.comp hc
    exact hC.mul hphid
  have hFi_compact (i : Fin d) : HasCompactSupport
      (fun x => A x * (fderiv ℝ phi x) (Pi.single i 1)) := by
    exact (hphi_compact.fderiv_apply ℝ (Pi.single i 1)).mul_left
  have hglobal (i : Fin d) :
      (∫ x, A x * (fderiv ℝ phi x) (Pi.single i 1) *
          (fderiv ℝ psi x) (Pi.single i 1)) =
        -∫ x, (fderiv ℝ
          (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1) * psi x := by
    let Fi : SpatialCoordinates d → ℝ :=
      fun x => A x * (fderiv ℝ phi x) (Pi.single i 1)
    have hFi_cont : Continuous Fi := (hAi i).continuous
    have hFi_deriv_cont : Continuous (fun x =>
        (fderiv ℝ Fi x) (Pi.single i 1)) := by
      have hp := (hAi i).continuous_fderiv_apply (by simp)
      exact hp.comp (continuous_id.prodMk continuous_const)
    have hphi_deriv_cont : Continuous (fun x =>
        (fderiv ℝ psi x) (Pi.single i 1)) :=
      (hpsi.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk continuous_const)
    have h1 : Integrable
        (fun x => (fderiv ℝ Fi x) (Pi.single i 1) * psi x)
        (volume : Measure (SpatialCoordinates d)) :=
      (hFi_deriv_cont.mul hpsi.continuous).integrable_of_hasCompactSupport
        ((hFi_compact i).fderiv_apply ℝ (Pi.single i 1)).mul_right
    have h2 : Integrable
        (fun x => Fi x * (fderiv ℝ psi x) (Pi.single i 1))
        (volume : Measure (SpatialCoordinates d)) :=
      (hFi_cont.mul hphi_deriv_cont).integrable_of_hasCompactSupport
        (hFi_compact i).mul_right
    have h3 : Integrable (fun x => Fi x * psi x)
        (volume : Measure (SpatialCoordinates d)) :=
      (hFi_cont.mul hpsi.continuous).integrable_of_hasCompactSupport
        (hFi_compact i).mul_right
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (f := Fi) (g := psi)
      (v := Pi.single i 1)
      h1 h2 h3
      (fun x _ => ((hAi i).differentiable (by simp)) x)
      (fun x _ => (hpsi.differentiable (by simp)) x)
    · simpa only [Fi] using hibp
  have hleft (i : Fin d) :
      (∫ x in Q, (fderiv ℝ
          (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1) * psi x) =
        ∫ x, (fderiv ℝ
          (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1) * psi x := by
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hpsi_zero x hx, mul_zero]
  have hright (i : Fin d) :
      (∫ x in Q, A x * (fderiv ℝ phi x) (Pi.single i 1) *
          (fderiv ℝ psi x) (Pi.single i 1)) =
        ∫ x, A x * (fderiv ℝ phi x) (Pi.single i 1) *
          (fderiv ℝ psi x) (Pi.single i 1) := by
    rw [← integral_indicator (centeredCube z r hr).isOpen.measurableSet]
    apply integral_congr_ae
    filter_upwards [hderiv_ae i] with x hx
    by_cases hqx : x ∈ Q
    · have hqx' : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
        simpa [Q] using hqx
      simp [Set.indicator_of_mem hqx']
    · have hqx' : x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
        simpa [Q] using hqx
      simp [Set.indicator_of_notMem hqx', hx hqx]
  have hcoord (i : Fin d) :
      -(∫ x in Q,
          (rho x)⁻¹ *
            (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
              (Pi.single i 1) * psi x
          ∂(cutoffSpeedMeasure M H omega N)) =
        ∫ x in Q, A x * (fderiv ℝ phi x) (Pi.single i 1) *
          (fderiv ℝ psi x) (Pi.single i 1) := by
    have hdens := setIntegral_withDensity_eq_setIntegral_toReal_smul
      (μ := (volume : Measure (SpatialCoordinates d)))
      (f := fun x => ENNReal.ofReal (rho x))
      hρmeas (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
      (fun x => (rho x)⁻¹ *
        (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
          (Pi.single i 1) * psi x)
      (centeredCube z r hr).isOpen.measurableSet
    have hdens' :
        (∫ x in Q, (rho x)⁻¹ *
          (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1) * psi x
          ∂(cutoffSpeedMeasure M H omega N)) =
          ∫ x in Q, rho x • ((rho x)⁻¹ *
            (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
              (Pi.single i 1) * psi x) := by
      rw [show cutoffSpeedMeasure M H omega N =
          volume.withDensity (fun x => ENNReal.ofReal (rho x)) by rfl]
      simpa [Q, ENNReal.toReal_ofReal (hρpos _).le, smul_eq_mul] using hdens
    rw [hdens']
    have hcancel (x : SpatialCoordinates d) :
        rho x • ((rho x)⁻¹ *
          (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1) * psi x) =
          (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1) * psi x := by
      dsimp only [smul_eq_mul]
      field_simp [ne_of_gt (hρpos x)]
    rw [integral_congr_ae (Filter.Eventually.of_forall hcancel)]
    rw [hleft i, ← hglobal i]
    exact (hright i).symm
  have hRHS_int (i : Fin d) : Integrable
      (fun x => A x * (fderiv ℝ phi x) (Pi.single i 1) *
        (fderiv ℝ psi x) (Pi.single i 1))
      (volume.restrict Q) := by
    have hcont : Continuous (fun x => A x * (fderiv ℝ phi x) (Pi.single i 1) *
        (fderiv ℝ psi x) (Pi.single i 1)) := by
      exact (hAi i).continuous.mul
        ((hpsi.continuous_fderiv_apply (by simp)).comp
          (continuous_id.prodMk continuous_const))
    have hcomp : HasCompactSupport
        (fun x => A x * (fderiv ℝ phi x) (Pi.single i 1) *
          (fderiv ℝ psi x) (Pi.single i 1)) :=
      (hFi_compact i).mul_right
    exact (hcont.integrable_of_hasCompactSupport hcomp).restrict
  have hL_int (i : Fin d) : Integrable
      (fun x => (rho x)⁻¹ *
        (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
          (Pi.single i 1) * psi x)
      ((cutoffSpeedMeasure M H omega N).restrict Q) := by
    rw [show cutoffSpeedMeasure M H omega N =
        volume.withDensity (fun x => ENNReal.ofReal (rho x)) by rfl]
    rw [restrict_withDensity (centeredCube z r hr).isOpen.measurableSet]
    rw [integrable_withDensity_iff_integrable_smul' hρmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hDcont : Continuous (fun x =>
        (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
          (Pi.single i 1)) := by
      exact ((hAi i).continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk continuous_const)
    have hDint : Integrable
        (fun x =>
          (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1) * psi x)
        (volume.restrict Q) := by
      have hglobalD : Integrable
          (fun x =>
            (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
              (Pi.single i 1) * psi x)
          (volume : Measure (SpatialCoordinates d)) :=
        (hDcont.mul hpsi.continuous).integrable_of_hasCompactSupport
          ((hFi_compact i).fderiv_apply ℝ (Pi.single i 1)).mul_right
      exact hglobalD.restrict
    apply (integrable_congr ?_).2 hDint
    filter_upwards [] with x
    rw [ENNReal.toReal_ofReal (hρpos x).le]
    dsimp only [smul_eq_mul]
    field_simp [ne_of_gt (hρpos x)]
  have hLsum :
      (∫ x in Q, (rho x)⁻¹ *
        (∑ i : Fin d,
          (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1)) * psi x
        ∂(cutoffSpeedMeasure M H omega N)) =
      ∑ i : Fin d, ∫ x in Q, (rho x)⁻¹ *
        (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
          (Pi.single i 1) * psi x
        ∂(cutoffSpeedMeasure M H omega N) := by
    have hsum := integral_finset_sum (μ :=
        (cutoffSpeedMeasure M H omega N).restrict Q)
      (Finset.univ : Finset (Fin d)) (fun i _ => hL_int i)
    rw [← hsum]
    apply integral_congr_ae
    filter_upwards [] with x
    calc
      ((rho x)⁻¹ * ∑ i : Fin d,
          (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1)) * psi x =
          (∑ i : Fin d, (rho x)⁻¹ *
            (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
              (Pi.single i 1)) * psi x := by rw [Finset.mul_sum]
      _ = ∑ i : Fin d, (rho x)⁻¹ *
          (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1) * psi x := by rw [Finset.sum_mul]
  have hRHSsum :
      (∫ x in Q, A x * ∑ i : Fin d,
          (fderiv ℝ phi x) (Pi.single i 1) *
            (fderiv ℝ psi x) (Pi.single i 1)) =
      ∑ i : Fin d, ∫ x in Q, A x *
        (fderiv ℝ phi x) (Pi.single i 1) *
          (fderiv ℝ psi x) (Pi.single i 1) := by
    have hsum := integral_finset_sum (μ := (volume.restrict Q))
      (Finset.univ : Finset (Fin d)) (fun i _ => hRHS_int i)
    rw [← hsum]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  calc
    -(∫ x in Q, (rho x)⁻¹ *
        (∑ i : Fin d,
          (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1)) * psi x
        ∂(cutoffSpeedMeasure M H omega N)) =
      -(∑ i : Fin d, ∫ x in Q, (rho x)⁻¹ *
        (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
          (Pi.single i 1) * psi x
        ∂(cutoffSpeedMeasure M H omega N)) := by rw [hLsum]
    _ = ∑ i : Fin d, (-(∫ x in Q, (rho x)⁻¹ *
        (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
          (Pi.single i 1) * psi x
        ∂(cutoffSpeedMeasure M H omega N))) := by
      rw [Finset.sum_neg_distrib]
    _ = ∑ i : Fin d, ∫ x in Q, A x *
        (fderiv ℝ phi x) (Pi.single i 1) *
          (fderiv ℝ psi x) (Pi.single i 1) := by
      exact Finset.sum_congr rfl (fun i _ => hcoord i)
    _ = ∫ x in Q, A x * ∑ i : Fin d,
        (fderiv ℝ phi x) (Pi.single i 1) *
      (fderiv ℝ psi x) (Pi.single i 1) := hRHSsum.symm

private theorem aux_finite_speed_resolvent_properties_occupation_bound
    {d : Nat} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (ν : Measure (DiffusionPath d)) [IsProbabilityMeasure ν]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (lam : ℝ) (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ)
    (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B) (hfb : ∀ x, |f x| ≤ B) :
    |∫ path, (∫ t in Set.Ioi (0 : ℝ),
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
        (centeredCube z r hr : Set (SpatialCoordinates d)) path}
        (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) ∂ν| ≤ B / lam := by
  have hpathbound (path : DiffusionPath d) :
      |∫ t in Set.Ioi (0 : ℝ), Set.indicator {s : ℝ | ENNReal.ofReal s <
        ContinuousPath.exitTime (centeredCube z r hr : Set (SpatialCoordinates d)) path}
        (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t| ≤ B / lam := by
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ t in Set.Ioi (0 : ℝ), Set.indicator {s : ℝ | ENNReal.ofReal s <
          ContinuousPath.exitTime (centeredCube z r hr : Set (SpatialCoordinates d)) path}
          (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t‖ ≤
          ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) * B := by
            apply norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi 0 hlam).mul_const B)
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            by_cases hmem : ENNReal.ofReal t <
                ContinuousPath.exitTime (centeredCube z r hr : Set (SpatialCoordinates d)) path
            · simp only [Set.indicator_apply, Set.mem_setOf_eq, if_pos hmem]
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
              exact mul_le_mul_of_nonneg_left (hfb _) (Real.exp_pos _).le
            · simp only [Set.indicator_apply, Set.mem_setOf_eq, if_neg hmem]
              simpa only [norm_zero] using (mul_nonneg (Real.exp_pos (-lam * t)).le hB)
      _ = B / lam := by
        rw [integral_mul_const, integral_exp_mul_Ioi (by linarith) 0]
        simp [Real.exp_zero]
        field_simp
  calc
    |∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
          (centeredCube z r hr : Set (SpatialCoordinates d)) path}
          (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) ∂ν| ≤
        (B / lam) * ν.real Set.univ := by
          rw [← Real.norm_eq_abs]
          apply norm_integral_le_of_norm_le_const
          exact Filter.Eventually.of_forall hpathbound
    _ = B / lam := by
      rw [measureReal_def, measure_univ]
      simp

private theorem aux_finite_speed_resolvent_properties_objective_gap
    (lam evv euv eu fvv fuu vv uv uu ed id : ℝ)
    (hfvv : fvv = euv + lam * uv)
    (hfuu : fuu = eu + lam * uu)
    (hed : ed = evv - 2 * euv + eu)
    (hid : id = vv - 2 * uv + uu) :
    (evv + lam * vv - 2 * fvv) - (eu + lam * uu - 2 * fuu) =
      ed + lam * id := by
  rw [hfvv, hfuu, hed, hid]
  ring

private theorem aux_finite_speed_resolvent_properties_square_integral_nonneg
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ) :
    0 ≤ ∫ x, g x ^ 2 ∂μ := by
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x => sq_nonneg (g x)))

private theorem aux_finite_speed_resolvent_properties_objective_lower
    (lam x y e i : ℝ) (hxy : x - y = e + lam * i)
    (he : 0 ≤ e) (hi : 0 ≤ i) (hlam : 0 ≤ lam) : y ≤ x := by
  have hli : 0 ≤ lam * i := mul_nonneg hlam hi
  linarith

private theorem aux_finite_speed_resolvent_properties_objective_integral_zero
    (lam x y e i : ℝ) (hxy : x - y = e + lam * i)
    (hobj : x = y) (he : 0 ≤ e) (hi : 0 ≤ i) (hlam : 0 < lam) :
    i = 0 := by
  have hsum : e + lam * i = 0 := by linarith
  have hli : 0 ≤ lam * i := mul_nonneg hlam.le hi
  have hli0 : lam * i = 0 := by linarith
  exact (mul_eq_zero.mp hli0).resolve_left (ne_of_gt hlam)

private theorem aux_finite_speed_resolvent_properties_square_ae_zero
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ)
    (hg : Integrable (fun x => g x ^ 2) μ)
    (hz : (∫ x, g x ^ 2 ∂μ) = 0) :
    ∀ᵐ x ∂μ, g x = 0 := by
  have hsq := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => sq_nonneg (g x))) hg).mp hz
  filter_upwards [hsq] with x hx
  exact sq_eq_zero_iff.mp hx

private theorem aux_finite_speed_resolvent_properties_ae_of_positive_density
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (rho : α → ℝ)
    (hrho : Measurable rho) (hpos : ∀ x, 0 < rho x) {p : α → Prop}
    (h : ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal (rho x)), p x) :
    ∀ᵐ x ∂μ, p x := by
  have h' := (ae_withDensity_iff hrho.ennreal_ofReal).mp h
  filter_upwards [h'] with x hx
  exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr (hpos x)))

private theorem aux_finite_speed_resolvent_properties_energy_nonneg_sub
    {d : Nat} {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (E : SobolevData Ω → SobolevData Ω → ℝ)
    (hE : ∀ a, 0 ≤ E a a) (v u : killedSobolevGraph Ω) :
    0 ≤ E (v - u : killedSobolevGraph Ω) (v - u : killedSobolevGraph Ω) := by
  exact hE _

private theorem aux_finite_speed_resolvent_properties_graph_square_integral_nonneg
    {d : Nat} {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (μ : Measure (SpatialCoordinates d)) (v u : killedSobolevGraph Ω) :
    0 ≤ ∫ x, ((((v : SobolevData Ω).1) x) - ((u : SobolevData Ω).1) x) ^ 2 ∂μ := by
  exact aux_finite_speed_resolvent_properties_square_integral_nonneg μ
    (fun x => ((v : SobolevData Ω).1) x - ((u : SobolevData Ω).1) x)

private theorem aux_finite_speed_resolvent_properties_square_integral_expansion
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (u v : α → ℝ)
    (hvv : Integrable (fun x => v x ^ 2) μ)
    (huv : Integrable (fun x => u x * v x) μ)
    (huu : Integrable (fun x => u x ^ 2) μ) :
    (∫ x, (v x - u x) ^ 2 ∂μ) =
      (∫ x, v x ^ 2 ∂μ) - 2 * (∫ x, u x * v x ∂μ) +
        (∫ x, u x ^ 2 ∂μ) := by
  have h2uv := huv.const_mul 2
  have hdiff : (fun x => (v x - u x) ^ 2) =ᵐ[μ]
      (fun x => v x ^ 2 - 2 * (u x * v x) + u x ^ 2) := by
    filter_upwards [] with x
    ring
  calc
    _ = ∫ x, v x ^ 2 - 2 * (u x * v x) + u x ^ 2 ∂μ :=
      integral_congr_ae hdiff
    _ = _ := by
      have hsub := hvv.sub h2uv
      have hadd := integral_add hsub huu
      calc
        _ = (∫ x, v x ^ 2 - 2 * (u x * v x) ∂μ) +
            ∫ x, u x ^ 2 ∂μ := by
              simpa only [Pi.add_apply] using! hadd
        _ = _ := by rw [integral_sub hvv h2uv, integral_const_mul]

private theorem aux_finite_speed_resolvent_properties_pointwise_energy_bound
    (lam B f u : ℝ) (hlam : 0 < lam) (hB : 0 ≤ B) (hfb : |f| ≤ B) :
    f * u - lam * u ^ 2 ≤ B ^ 2 / lam := by
  have hfupper : f ≤ B := (le_abs_self f).trans hfb
  have hflower : -B ≤ f := (neg_le_neg hfb).trans (neg_abs_le f)
  apply (le_div_iff₀ hlam).2
  by_cases hu : 0 ≤ u
  · have hfu : f * u ≤ B * u := mul_le_mul_of_nonneg_right hfupper hu
    have hfu' := mul_le_mul_of_nonneg_left hfu hlam.le
    have hsquare := sq_nonneg (2 * lam * u - B)
    nlinarith
  · have hu' : u ≤ 0 := le_of_not_ge hu
    have hfu : f * u ≤ (-B) * u := mul_le_mul_of_nonpos_right hflower hu'
    have hfu' := mul_le_mul_of_nonneg_left hfu hlam.le
    have hsquare := sq_nonneg (2 * lam * u + B)
    nlinarith

private theorem aux_finite_speed_resolvent_properties_integral_sub_const_mul
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (lam : ℝ)
    (p q : α → ℝ) (hp : Integrable p μ) (hq : Integrable q μ) :
    (∫ x, p x - lam * q x ∂μ) =
      (∫ x, p x ∂μ) - lam * (∫ x, q x ∂μ) := by
  rw [integral_sub hp (hq.const_mul lam), integral_const_mul]

private theorem aux_finite_speed_resolvent_properties_integral_const_restrict
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    (hs : MeasurableSet s) (c : ℝ) :
    (∫ x in s, c ∂μ) = c * (μ s).toReal := by
  rw [integral_const]
  simp [measureReal_def, hs]
  ring

private theorem aux_finite_speed_resolvent_properties_energy_eq_of_source
    (lam e f q i : ℝ) (hs : f = e + lam * q)
    (hi : i = f - lam * q) : e = i := by
  linarith

private theorem aux_finite_speed_resolvent_properties_division_rearrange
    (B m lam : ℝ) : (B ^ 2 / lam) * m = B ^ 2 * m / lam := by
  ring



private theorem aux_finite_speed_resolvent_properties_graph_ext
    {d : Nat} {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (v u : killedSobolevGraph Ω)
    (hfirst : (v : SobolevData Ω).1 = (u : SobolevData Ω).1) : v = u := by
  let w : SobolevData Ω := ((v - u : killedSobolevGraph Ω) : SobolevData Ω)
  have hw : w ∈ weakSobolevGraph Ω := by
    dsimp [w]
    exact killedSobolevGraph_le_weakSobolevGraph ((v - u : killedSobolevGraph Ω).property)
  have hw0 : w.1 = 0 := by
    dsimp [w]
    change (v : SobolevData Ω).1 - (u : SobolevData Ω).1 = 0
    exact sub_eq_zero.mpr hfirst
  have hwweak : (0, w.2) ∈ weakSobolevGraph Ω := by
    have heq : w = (0, w.2) := by
      apply Prod.ext
      · exact hw0
      · rfl
    exact heq ▸ hw
  have hwgrad := weakSobolevGraph_gradient_eq_zero hwweak
  have hgrad : (v : SobolevData Ω).2 = (u : SobolevData Ω).2 := by
    have hdiffgrad : (v : SobolevData Ω).2 - (u : SobolevData Ω).2 = 0 := by
      simpa [w] using hwgrad
    exact sub_eq_zero.mp hdiffgrad
  apply Subtype.ext
  apply Prod.ext
  · exact hfirst
  · exact hgrad



private theorem aux_finite_speed_resolvent_properties_energy_upper
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α) (hsmeas : MeasurableSet s)
    (lam B e : ℝ) (hlam : 0 < lam) (hB : 0 ≤ B)
    (f uu : α → ℝ) (hfb : ∀ x, |f x| ≤ B)
    (hFU : Integrable (fun x => f x * uu x) (μ.restrict s))
    (hUU : Integrable (fun x => uu x ^ 2) (μ.restrict s))
    (hcst : Integrable (fun _ : α => B ^ 2 / lam) (μ.restrict s))
    (hsrc : (∫ x in s, f x * uu x ∂μ) = e + lam * ∫ x in s, uu x ^ 2 ∂μ) :
    e ≤ B ^ 2 * (μ s).toReal / lam := by
  have hpoint : ∀ x, f x * uu x - lam * uu x ^ 2 ≤ B ^ 2 / lam := fun x =>
    aux_finite_speed_resolvent_properties_pointwise_energy_bound lam B (f x) (uu x)
      hlam hB (hfb x)
  have hleft : Integrable (fun x => f x * uu x - lam * uu x ^ 2) (μ.restrict s) := by
    simpa only [Pi.sub_apply] using! hFU.sub (hUU.const_mul lam)
  have hmono := integral_mono_ae hleft hcst (Filter.Eventually.of_forall hpoint)
  have hsplit : (∫ x in s, f x * uu x - lam * uu x ^ 2 ∂μ) =
      (∫ x in s, f x * uu x ∂μ) - lam * ∫ x in s, uu x ^ 2 ∂μ :=
    aux_finite_speed_resolvent_properties_integral_sub_const_mul (μ.restrict s) lam
      (fun x => f x * uu x) (fun x => uu x ^ 2) hFU hUU
  have hEeq : e = ∫ x in s, f x * uu x - lam * uu x ^ 2 ∂μ :=
    aux_finite_speed_resolvent_properties_energy_eq_of_source (lam := lam)
      (hs := hsrc) (hi := hsplit)
  have hconst_eval : (∫ x in s, B ^ 2 / lam ∂μ) = (B ^ 2 / lam) * (μ s).toReal :=
    aux_finite_speed_resolvent_properties_integral_const_restrict μ s hsmeas (B ^ 2 / lam)
  calc
    e = ∫ x in s, f x * uu x - lam * uu x ^ 2 ∂μ := hEeq
    _ ≤ ∫ x in s, B ^ 2 / lam ∂μ := hmono
    _ = B ^ 2 * (μ s).toReal / lam := by
      rw [hconst_eval]
      exact aux_finite_speed_resolvent_properties_division_rearrange B (μ s).toReal lam

private theorem aux_finite_speed_resolvent_properties_source_split
    {α : Type*} [MeasurableSpace α] (ν : Measure α) (lam e : ℝ)
    (f uu vv : α → ℝ)
    (hfv : Integrable (fun x => f x * vv x) ν)
    (huv : Integrable (fun x => uu x * vv x) ν)
    (hw : e = ∫ x, (f x - lam * uu x) * vv x ∂ν) :
    (∫ x, f x * vv x ∂ν) = e + lam * ∫ x, uu x * vv x ∂ν := by
  have hLamuv : Integrable (fun x => lam * uu x * vv x) ν := by
    simpa [mul_assoc] using huv.const_mul lam
  have hsplit : (∫ x, (f x - lam * uu x) * vv x ∂ν) =
      (∫ x, f x * vv x ∂ν) - lam * ∫ x, uu x * vv x ∂ν := by
    have heq : (fun x => (f x - lam * uu x) * vv x) =ᵐ[ν]
        (fun x => f x * vv x - lam * uu x * vv x) := by
      filter_upwards [] with x
      ring
    calc
      _ = ∫ x, f x * vv x - lam * uu x * vv x ∂ν := integral_congr_ae heq
      _ = _ := by
        rw [integral_sub hfv hLamuv]
        congr 1
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with x
        ring
  rw [hsplit] at hw
  linarith

private theorem aux_finite_speed_resolvent_properties_speed_density_pos
    {d : Nat}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : Nat) (x : SpatialCoordinates d) :
    0 < cutoffSpeedDensity M H omega N x := by
  dsimp [cutoffSpeedDensity]
  positivity

private theorem aux_finite_speed_resolvent_properties_speed_density_continuous
    {d : Nat}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : Nat) :
    Continuous (cutoffSpeedDensity M H omega N) := by
  have hpot : Continuous (cutoffPotential H omega N) := by
    unfold cutoffPotential
    fun_prop
  unfold cutoffSpeedDensity
  exact Real.continuous_exp.comp (hpot.sub continuous_const)



private theorem aux_finite_speed_resolvent_properties_speed_integrable
    {d : Nat}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : Nat)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    {g : SpatialCoordinates d → ℝ}
    (hg : Integrable g
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    Integrable g ((cutoffSpeedMeasure M H omega N).restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hQmeas : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hrho_pos := aux_finite_speed_resolvent_properties_speed_density_pos M H omega N
  have hrho_cont := aux_finite_speed_resolvent_properties_speed_density_continuous M H omega N
  obtain ⟨C, hCbound⟩ :=
    (isCompact_closedBall z (r / 2)).exists_bound_of_continuousOn hrho_cont.continuousOn
  have hrho_bound : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      ‖cutoffSpeedDensity M H omega N x‖ ≤ C := by
    filter_upwards [ae_restrict_mem hQmeas] with x hx
    apply hCbound x
    have hxball : x ∈ Metric.ball z (r / 2) := by
      simpa [centeredCube] using hx
    exact Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hxball))
  rw [show cutoffSpeedMeasure M H omega N =
      volume.withDensity (fun x => ENNReal.ofReal (cutoffSpeedDensity M H omega N x)) by rfl]
  rw [restrict_withDensity hQmeas]
  rw [integrable_withDensity_iff_integrable_smul' hrho_cont.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hm := hg.bdd_mul hrho_cont.aestronglyMeasurable hrho_bound
  apply (integrable_congr ?_).2 hm
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (hrho_pos x).le]
  rfl



private theorem aux_finite_speed_resolvent_properties_ae_speed_to_volume
    {d : Nat}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : Nat)
    (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S)
    {p : SpatialCoordinates d → Prop}
    (h : ∀ᵐ x ∂((cutoffSpeedMeasure M H omega N).restrict S), p x) :
    ∀ᵐ x ∂(volume.restrict S), p x := by
  have hrho_pos := aux_finite_speed_resolvent_properties_speed_density_pos M H omega N
  have hrho_cont := aux_finite_speed_resolvent_properties_speed_density_continuous M H omega N
  have hdens : ∀ᵐ x ∂((volume.restrict S).withDensity
      (fun x => ENNReal.ofReal (cutoffSpeedDensity M H omega N x))), p x := by
    rw [← restrict_withDensity hS]
    simpa [cutoffSpeedMeasure] using! h
  exact aux_finite_speed_resolvent_properties_ae_of_positive_density
    (volume.restrict S) (cutoffSpeedDensity M H omega N) hrho_cont.measurable hrho_pos hdens



theorem finite_speed_resolvent_properties
    {d : Nat} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (hcoeffC1 : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : Nat,
      ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (PN : Nat → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : Nat → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (hinput : aux_cutoff_lifetime_package_LocalInput M H KN)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (E : Nat → BilateralField d → SobolevData (centeredCube z r hr) →
      SobolevData (centeredCube z r hr) → ℝ)
    (hE : ∀ N omega u v, E N omega u v =
      sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr) u v)
    (R : Nat → BilateralField d → ℝ → (SpatialCoordinates d → ℝ) → SpatialCoordinates d → ℝ)
    (hR : ∀ N omega lam f x, R N omega lam f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
          (centeredCube z r hr : Set (SpatialCoordinates d)) path}
          (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
        ∂(KN N (omega, x)))
    (L : Nat → BilateralField d → (SpatialCoordinates d → ℝ) → SpatialCoordinates d → ℝ)
    (hL : ∀ N omega phi x, L N omega phi x =
      (cutoffSpeedDensity M H omega N x)⁻¹ * ∑ i : Fin d,
        (fderiv ℝ (fun y => cutoffCoefficient M H omega N y *
          (fderiv ℝ phi y) (Pi.single i 1)) x) (Pi.single i 1))
    (hstop :
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : Nat,
        ∀ (x : SpatialCoordinates d) (phi : SpatialCoordinates d → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) phi →
          HasCompactSupport phi →
          Function.support phi ⊆
            (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ t : ℝ≥0,
            ∫ path,
              (phi (path (ContinuousPath.exitTimeTrunc
                (centeredCube z r hr : Set (SpatialCoordinates d)) t path)) -
                phi x -
                ∫ s in Set.Icc (0 : ℝ)
                    ((ContinuousPath.exitTimeTrunc
                      (centeredCube z r hr : Set (SpatialCoordinates d)) t path) : ℝ),
                  L N omega phi (path (Real.toNNReal s)))
              ∂(KN N (omega, x)) = 0) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : Nat,
      (∀ phi psi : SpatialCoordinates d → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) phi → ContDiff ℝ (⊤ : ℕ∞) psi →
        HasCompactSupport phi → HasCompactSupport psi →
        Function.support phi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        Function.support psi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        -(∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          L N omega phi x * psi x ∂(cutoffSpeedMeasure M H omega N)) =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          cutoffCoefficient M H omega N x * (∑ i : Fin d,
            (fderiv ℝ phi x) (Pi.single i 1) * (fderiv ℝ psi x) (Pi.single i 1))) ∧
      (∀ (lam : ℝ), 0 < lam → ∀ (f : SpatialCoordinates d → ℝ), Measurable f →
        ∀ (B : ℝ), 0 ≤ B → (∀ x, |f x| ≤ B) →
        (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
          |R N omega lam f x| ≤ B / lam) ∧
        ∃ u : killedSobolevGraph (centeredCube z r hr),
          (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
            ((u : SobolevData (centeredCube z r hr)).1) x = R N omega lam f x) ∧
          (∀ v : killedSobolevGraph (centeredCube z r hr),
            E N omega (u : SobolevData (centeredCube z r hr))
              (v : SobolevData (centeredCube z r hr)) =
            ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              (f x - lam * ((u : SobolevData (centeredCube z r hr)).1) x) *
                ((v : SobolevData (centeredCube z r hr)).1) x
                ∂(cutoffSpeedMeasure M H omega N)) ∧
          (IsLeast (Set.range (fun v : killedSobolevGraph (centeredCube z r hr) =>
            (E N omega (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)) + lam * (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (((v : SobolevData (centeredCube z r hr)).1) x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)) - 2 * (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x * ((v : SobolevData (centeredCube z r hr)).1) x ∂(cutoffSpeedMeasure M H omega N)))))
            (E N omega (u : SobolevData (centeredCube z r hr)) (u : SobolevData (centeredCube z r hr)) + lam * (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (((u : SobolevData (centeredCube z r hr)).1) x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)) - 2 * (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x * ((u : SobolevData (centeredCube z r hr)).1) x ∂(cutoffSpeedMeasure M H omega N))) ∧
          (∀ v : killedSobolevGraph (centeredCube z r hr),
            (E N omega (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)) + lam * (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (((v : SobolevData (centeredCube z r hr)).1) x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)) - 2 * (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x * ((v : SobolevData (centeredCube z r hr)).1) x ∂(cutoffSpeedMeasure M H omega N))) =
            (E N omega (u : SobolevData (centeredCube z r hr)) (u : SobolevData (centeredCube z r hr)) + lam * (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (((u : SobolevData (centeredCube z r hr)).1) x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)) - 2 * (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x * ((u : SobolevData (centeredCube z r hr)).1) x ∂(cutoffSpeedMeasure M H omega N))) → v = u)) ∧
            E N omega (u : SobolevData (centeredCube z r hr))
            (u : SobolevData (centeredCube z r hr)) ≤
            B ^ 2 * (cutoffSpeedMeasure M H omega N (centeredCube z r hr : Set (SpatialCoordinates d))).toReal / lam) := by
  obtain ⟨Lpath, hLpath, hLlocal, hLstrong⟩ := aux_cutoff_lifetime_package_local M H KN hinput
  have hSymm := prop_limit_properties_cutoff_symmetry M H PN KN hin Lpath hLpath hLlocal hLstrong
  have hbridge := finite_speed_resolvent_killed_bridge hd M H hH PN KN hKN hin z r hr
    E hE R hR L hL hstop hSymm
  filter_upwards [hcoeffC1, hbridge] with omega hC hBr
  intro N
  have hnorm := killed_generator_normalization M H omega N z r hr
  refine ⟨?_, ?_⟩
  · intro phi psi hphi hpsi hphi_compact hpsi_compact hphi_support hpsi_support
    have hibp := aux_finite_speed_resolvent_properties_ibp hd M H omega N z r hr
      (hC N) hnorm.1 phi psi hphi hpsi hphi_compact hpsi_compact hphi_support hpsi_support
    simpa only [hL N omega phi] using hibp
  · intro lam hlam f hf B hB hfb
    have hbound : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        |R N omega lam f x| ≤ B / lam := by
      intro x hx
      rw [hR N omega lam f x]
      letI : IsMarkovKernel (KN N) := hKN N
      letI : IsProbabilityMeasure (KN N (omega, x)) :=
        IsMarkovKernel.isProbabilityMeasure (omega, x)
      exact aux_finite_speed_resolvent_properties_occupation_bound
        (KN N (omega, x)) z r hr lam hlam f hf B hB hfb
    obtain ⟨u, huR, hweak⟩ := hBr N lam hlam f hf B hB hfb
    let hQ : Set (SpatialCoordinates d) := centeredCube z r hr
    have hQmeas : MeasurableSet hQ := by
      simpa [hQ] using (centeredCube z r hr).isOpen.measurableSet
    have hQvol : IsFiniteMeasure (volume.restrict hQ) := by
      apply isFiniteMeasure_restrict.mpr
      have htop := measure_ball_lt_top (μ := (volume : Measure (SpatialCoordinates d)))
        (x := z) (r := r / 2)
      simpa [hQ, centeredCube] using htop.ne
    letI : IsFiniteMeasure (volume.restrict hQ) := hQvol
    have hspeed_integrable {g : SpatialCoordinates d → ℝ}
        (hg : Integrable g (volume.restrict hQ)) :
        Integrable g ((cutoffSpeedMeasure M H omega N).restrict hQ) :=
      aux_finite_speed_resolvent_properties_speed_integrable M H omega N z r hr hg
    have hmemU : MemLp
        (((u : SobolevData (centeredCube z r hr)).1 : DomainL2 (centeredCube z r hr)) :
          SpatialCoordinates d → ℝ) 2 (volume.restrict hQ) := by
      simpa [hQ] using (Lp.memLp
        ((u : SobolevData (centeredCube z r hr)).1 : DomainL2 (centeredCube z r hr)))
    have hUint : Integrable
        (((u : SobolevData (centeredCube z r hr)).1 : DomainL2 (centeredCube z r hr)) :
          SpatialCoordinates d → ℝ) (volume.restrict hQ) :=
      hmemU.integrable (by norm_num)
    have hUUspeed : Integrable
        (fun x => (((u : SobolevData (centeredCube z r hr)).1) x) ^ 2)
        ((cutoffSpeedMeasure M H omega N).restrict hQ) := by
      apply hspeed_integrable
      have hm := hmemU.integrable_mul hmemU
      simpa [pow_two] using! hm
    have hFUspeed : Integrable
        (fun x => f x * ((u : SobolevData (centeredCube z r hr)).1) x)
        ((cutoffSpeedMeasure M H omega N).restrict hQ) := by
      apply hspeed_integrable
      exact hUint.bdd_mul hf.stronglyMeasurable.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hfb x)
    have hmemV (v : killedSobolevGraph (centeredCube z r hr)) : MemLp
        (((v : SobolevData (centeredCube z r hr)).1 : DomainL2 (centeredCube z r hr)) :
          SpatialCoordinates d → ℝ) 2 (volume.restrict hQ) := by
      simpa [hQ] using (Lp.memLp
        ((v : SobolevData (centeredCube z r hr)).1 : DomainL2 (centeredCube z r hr)))
    have hVint (v : killedSobolevGraph (centeredCube z r hr)) : Integrable
        (((v : SobolevData (centeredCube z r hr)).1 : DomainL2 (centeredCube z r hr)) :
          SpatialCoordinates d → ℝ) (volume.restrict hQ) :=
      (hmemV v).integrable (by norm_num)
    have hVVs (v : killedSobolevGraph (centeredCube z r hr)) : Integrable
        (fun x => (((v : SobolevData (centeredCube z r hr)).1) x) ^ 2)
        ((cutoffSpeedMeasure M H omega N).restrict hQ) := by
      apply hspeed_integrable
      have hm := (hmemV v).integrable_mul (hmemV v)
      simpa [pow_two] using! hm
    have hFVs (v : killedSobolevGraph (centeredCube z r hr)) : Integrable
        (fun x => f x * ((v : SobolevData (centeredCube z r hr)).1) x)
        ((cutoffSpeedMeasure M H omega N).restrict hQ) := by
      apply hspeed_integrable
      exact (hVint v).bdd_mul hf.stronglyMeasurable.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hfb x)
    have hUVs (v : killedSobolevGraph (centeredCube z r hr)) : Integrable
        (fun x => (((u : SobolevData (centeredCube z r hr)).1) x) *
          ((v : SobolevData (centeredCube z r hr)).1) x)
        ((cutoffSpeedMeasure M H omega N).restrict hQ) := by
      apply hspeed_integrable
      exact (hmemU.integrable_mul (hmemV v))
    have hsource (v : killedSobolevGraph (centeredCube z r hr)) :
        (∫ x in hQ, f x * ((v : SobolevData (centeredCube z r hr)).1) x
            ∂(cutoffSpeedMeasure M H omega N)) =
          E N omega (u : SobolevData (centeredCube z r hr))
            (v : SobolevData (centeredCube z r hr)) +
            lam * (∫ x in hQ,
              (((u : SobolevData (centeredCube z r hr)).1) x) *
                ((v : SobolevData (centeredCube z r hr)).1) x
              ∂(cutoffSpeedMeasure M H omega N)) :=
      aux_finite_speed_resolvent_properties_source_split
        ((cutoffSpeedMeasure M H omega N).restrict hQ) lam
        (E N omega (u : SobolevData (centeredCube z r hr))
          (v : SobolevData (centeredCube z r hr)))
        f (fun x => ((u : SobolevData (centeredCube z r hr)).1) x)
        (fun x => ((v : SobolevData (centeredCube z r hr)).1) x)
        (hFVs v) (hUVs v) (hweak v)
    have hnonneg (a : SobolevData (centeredCube z r hr)) :
        0 ≤ E N omega a a := by
      rw [hE]
      exact sobolevCoefficientForm_nonneg _ _
    let aOuter := Lane4.cutoffPositiveCoefficient M H omega N z hr
    have hformgapOuter (v : killedSobolevGraph (centeredCube z r hr)) :
        sobolevCoefficientForm aOuter
            ((v - u : killedSobolevGraph (centeredCube z r hr)) :
              SobolevData (centeredCube z r hr))
            ((v - u : killedSobolevGraph (centeredCube z r hr)) :
              SobolevData (centeredCube z r hr)) =
          sobolevCoefficientForm aOuter (v : SobolevData (centeredCube z r hr))
            (v : SobolevData (centeredCube z r hr)) -
            2 * sobolevCoefficientForm aOuter (u : SobolevData (centeredCube z r hr))
              (v : SobolevData (centeredCube z r hr)) +
            sobolevCoefficientForm aOuter (u : SobolevData (centeredCube z r hr))
              (u : SobolevData (centeredCube z r hr)) := by
      have hg := bilinear_source_objective_gap
        (sobolevCoefficientForm aOuter) (sobolevCoefficientForm_symm aOuter)
        (sobolevCoefficientForm aOuter (u : SobolevData (centeredCube z r hr)))
        (u : SobolevData (centeredCube z r hr)) (fun w => rfl)
        (v : SobolevData (centeredCube z r hr))
      rw [Submodule.coe_sub]
      linarith
    have hEgapOuter (v : killedSobolevGraph (centeredCube z r hr)) :
        E N omega ((v - u : killedSobolevGraph (centeredCube z r hr)) :
            SobolevData (centeredCube z r hr))
          ((v - u : killedSobolevGraph (centeredCube z r hr)) :
            SobolevData (centeredCube z r hr)) =
          E N omega (v : SobolevData (centeredCube z r hr))
            (v : SobolevData (centeredCube z r hr)) -
            2 * E N omega (u : SobolevData (centeredCube z r hr))
              (v : SobolevData (centeredCube z r hr)) +
            E N omega (u : SobolevData (centeredCube z r hr))
              (u : SobolevData (centeredCube z r hr)) := by
      simpa only [hE, aOuter] using hformgapOuter v
    have hdiffsqOuter (v : killedSobolevGraph (centeredCube z r hr)) : Integrable
        (fun x => ((((v : SobolevData (centeredCube z r hr)).1) x) -
          (((u : SobolevData (centeredCube z r hr)).1) x)) ^ 2)
        ((cutoffSpeedMeasure M H omega N).restrict hQ) := by
      apply hspeed_integrable
      have hdiffmem := (hmemV v).sub hmemU
      have hm := hdiffmem.integrable_mul hdiffmem
      simpa only [pow_two] using! hm
    have hIsqOuter (v : killedSobolevGraph (centeredCube z r hr)) :
        (∫ x in hQ, ((((v : SobolevData (centeredCube z r hr)).1) x) -
          (((u : SobolevData (centeredCube z r hr)).1) x)) ^ 2
          ∂(cutoffSpeedMeasure M H omega N)) =
          (∫ x in hQ, (((v : SobolevData (centeredCube z r hr)).1) x) ^ 2
            ∂(cutoffSpeedMeasure M H omega N)) -
          2 * (∫ x in hQ, (((u : SobolevData (centeredCube z r hr)).1) x) *
            ((v : SobolevData (centeredCube z r hr)).1) x
            ∂(cutoffSpeedMeasure M H omega N)) +
          (∫ x in hQ, (((u : SobolevData (centeredCube z r hr)).1) x) ^ 2
            ∂(cutoffSpeedMeasure M H omega N)) := by
      exact aux_finite_speed_resolvent_properties_square_integral_expansion
        ((cutoffSpeedMeasure M H omega N).restrict hQ)
        (fun x => (((u : SobolevData (centeredCube z r hr)).1) x))
        (fun x => (((v : SobolevData (centeredCube z r hr)).1) x))
        (hVVs v) (hUVs v) hUUspeed
    have hsource_uOuter := hsource u
    have hUUeq :
        (∫ x in hQ, (((u : SobolevData (centeredCube z r hr)).1) x) *
          ((u : SobolevData (centeredCube z r hr)).1) x
          ∂(cutoffSpeedMeasure M H omega N)) =
        (∫ x in hQ, (((u : SobolevData (centeredCube z r hr)).1) x) ^ 2
          ∂(cutoffSpeedMeasure M H omega N)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    have hsource_u2 := hsource_uOuter
    rw [hUUeq] at hsource_u2
    have hgapOuter (v : killedSobolevGraph (centeredCube z r hr)) :
        (E N omega (v : SobolevData (centeredCube z r hr))
            (v : SobolevData (centeredCube z r hr)) +
          lam * (∫ x in hQ, (((v : SobolevData (centeredCube z r hr)).1) x) ^ 2
            ∂(cutoffSpeedMeasure M H omega N)) -
          2 * (∫ x in hQ, f x * ((v : SobolevData (centeredCube z r hr)).1) x
            ∂(cutoffSpeedMeasure M H omega N))) -
        (E N omega (u : SobolevData (centeredCube z r hr))
            (u : SobolevData (centeredCube z r hr)) +
          lam * (∫ x in hQ, (((u : SobolevData (centeredCube z r hr)).1) x) ^ 2
            ∂(cutoffSpeedMeasure M H omega N)) -
          2 * (∫ x in hQ, f x * ((u : SobolevData (centeredCube z r hr)).1) x
            ∂(cutoffSpeedMeasure M H omega N))) =
          E N omega ((v - u : killedSobolevGraph (centeredCube z r hr)) :
            SobolevData (centeredCube z r hr))
            ((v - u : killedSobolevGraph (centeredCube z r hr)) :
              SobolevData (centeredCube z r hr)) +
          lam * (∫ x in hQ, ((((v : SobolevData (centeredCube z r hr)).1) x) -
            (((u : SobolevData (centeredCube z r hr)).1) x)) ^ 2
            ∂(cutoffSpeedMeasure M H omega N)) := by
      exact aux_finite_speed_resolvent_properties_objective_gap
        (lam := lam) (hfvv := hsource v) (hfuu := hsource_u2)
        (hed := hEgapOuter v) (hid := hIsqOuter v)
    refine ⟨hbound, u, huR, hweak, ?_⟩
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · let Obj : killedSobolevGraph (centeredCube z r hr) → ℝ := fun w =>
          E N omega (w : SobolevData (centeredCube z r hr))
              (w : SobolevData (centeredCube z r hr)) +
            lam * (∫ x in hQ,
              (((w : SobolevData (centeredCube z r hr)).1) x) ^ 2
                ∂(cutoffSpeedMeasure M H omega N)) -
            2 * (∫ x in hQ, f x *
              ((w : SobolevData (centeredCube z r hr)).1) x
                ∂(cutoffSpeedMeasure M H omega N))
        change IsLeast (Set.range Obj) (Obj u)
        constructor
        · exact ⟨u, rfl⟩
        · rintro x ⟨v, rfl⟩
          dsimp [Obj]
          have hnonE := aux_finite_speed_resolvent_properties_energy_nonneg_sub
            (fun a b => E N omega a b) (fun a => hnonneg a) v u
          have hnonI :=
            aux_finite_speed_resolvent_properties_graph_square_integral_nonneg
              ((cutoffSpeedMeasure M H omega N).restrict hQ) v u
          exact aux_finite_speed_resolvent_properties_objective_lower
            (lam := lam) (hxy := hgapOuter v) (he := hnonE) (hi := hnonI)
            (hlam := le_of_lt hlam)
      · intro v hv
        have hnonE := aux_finite_speed_resolvent_properties_energy_nonneg_sub
          (fun a b => E N omega a b) (fun a => hnonneg a) v u
        have hnonI :=
          aux_finite_speed_resolvent_properties_graph_square_integral_nonneg
            ((cutoffSpeedMeasure M H omega N).restrict hQ) v u
        have hIzero := aux_finite_speed_resolvent_properties_objective_integral_zero
          (lam := lam) (hxy := hgapOuter v) (hobj := hv)
          (he := hnonE) (hi := hnonI) (hlam := hlam)
        have hsqae := aux_finite_speed_resolvent_properties_square_ae_zero
          ((cutoffSpeedMeasure M H omega N).restrict hQ)
          (fun x => (((v : SobolevData (centeredCube z r hr)).1) x) -
            (((u : SobolevData (centeredCube z r hr)).1) x))
          (hdiffsqOuter v) hIzero
        have hVU_speed : ∀ᵐ x ∂(cutoffSpeedMeasure M H omega N).restrict hQ,
            ((v : SobolevData (centeredCube z r hr)).1) x =
              ((u : SobolevData (centeredCube z r hr)).1) x := by
          filter_upwards [hsqae] with x hx
          exact sub_eq_zero.mp hx
        have hVU_vol := aux_finite_speed_resolvent_properties_ae_speed_to_volume
          M H omega N hQ hQmeas hVU_speed
        have hfirst :
            (v : SobolevData (centeredCube z r hr)).1 =
              (u : SobolevData (centeredCube z r hr)).1 := by
          apply Lp.ext
          simpa [hQ] using! hVU_vol
        exact aux_finite_speed_resolvent_properties_graph_ext v u hfirst
    · have hcst : Integrable (fun _ : SpatialCoordinates d => B ^ 2 / lam)
          ((cutoffSpeedMeasure M H omega N).restrict hQ) :=
        hspeed_integrable (integrable_const _)
      exact aux_finite_speed_resolvent_properties_energy_upper
        (cutoffSpeedMeasure M H omega N) hQ hQmeas lam B
        (E N omega (u : SobolevData (centeredCube z r hr))
          (u : SobolevData (centeredCube z r hr)))
        hlam hB f (fun x => ((u : SobolevData (centeredCube z r hr)).1) x) hfb
        hFUspeed hUUspeed hcst hsource_u2

end Paper
