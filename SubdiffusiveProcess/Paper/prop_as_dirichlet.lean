module

public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.lem_finite_stopping
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.Paper.working_levels_ratio
public import SubdiffusiveProcess.Paper.lem_local_normalizations
public import SubdiffusiveProcess.Paper.inputs_EM_witness

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess
open Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_prop_as_dirichlet_lower_bound
    {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0,
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient
            (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr))
    (phi : SpatialCoordinates d → ℝ)
    (hphi : ContDiff ℝ ∞ phi)
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (u : weakSobolevGraph (centeredCube z r hr))
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)))
    (huU : ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U)
    (hbdry : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      U x = phi x)
    (e : ℝ)
    (he : e = sobolevCoefficientForm a u.val u.val) :
    dirichletResponse (killedResponseSpace hP) a b ≤ e := by
  let v : weakSobolevGraph (centeredCube z r hr) :=
    ⟨u.val - b.val, (weakSobolevGraph (centeredCube z r hr)).sub_mem
      u.property b.property⟩
  have hvU : ContinuousOn (U - phi) (closedCube z r hr : Set (SpatialCoordinates d)) :=
    hU.sub hphi.continuous.continuousOn
  have hvrep : ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] (U - phi) := by
    filter_upwards [Lp.coeFn_sub u.val.1 b.val.1, huU, hb] with x hsub hxu hxb
    change ((u.val.1 - b.val.1 : DomainL2 (centeredCube z r hr)) :
      SpatialCoordinates d → ℝ) x = U x - phi x
    calc
      ((u.val.1 - b.val.1 : DomainL2 (centeredCube z r hr)) :
          SpatialCoordinates d → ℝ) x =
          ((u.val.1 : SpatialCoordinates d → ℝ) x -
            (b.val.1 : SpatialCoordinates d → ℝ) x) := hsub
      _ = U x - phi x := by rw [hxu, hxb]
  have hvzero : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      (U - phi) x = 0 := by
    intro x hx
    simp only [Pi.sub_apply]
    rw [hbdry x hx]
    ring
  have hvk : (v : SobolevData (centeredCube z r hr)) ∈
      killedSobolevGraph (centeredCube z r hr) := by
    exact lem_extension_trace_class_transport hd z r hr v (U - phi) hvU hvrep hvzero
  let w : (killedResponseSpace hP).space :=
    ⟨v.val, hvk⟩
  have hsum : b.val + w.val = u.val := by
    change b.val + (u.val - b.val) = u.val
    abel
  have hleast := dirichletResponse_isLeast (killedResponseSpace hP) a b
  have hle := hleast.2 ⟨w, rfl⟩
  change dirichletResponse (killedResponseSpace hP) a b ≤
    sobolevCoefficientForm a (b.val + w.val) (b.val + w.val) at hle
  rw [hsum] at hle
  exact he ▸ hle

open scoped Distributions in
/-- Smooth compactly supported data give admissible continuous competitors:
the energy of `b + smoothSobolevData ψ` lies in the continuous-boundary set. -/
theorem aux_prop_as_dirichlet_smooth_competitor
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr))
    (phi : SpatialCoordinates d → ℝ)
    (hphi : ContDiff ℝ ∞ phi)
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (ψ : 𝓓(centeredCube z r hr, ℝ)) :
    sobolevCoefficientForm a (b.val + smoothSobolevData ψ) (b.val + smoothSobolevData ψ) ∈
      {e : ℝ | ∃ (u : weakSobolevGraph (centeredCube z r hr))
          (U : SpatialCoordinates d → ℝ),
        ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
        ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
          U x = phi x) ∧
        e = sobolevCoefficientForm a u.val u.val} := by
  let u : weakSobolevGraph (centeredCube z r hr) :=
    ⟨b.val + smoothSobolevData ψ,
      (weakSobolevGraph (centeredCube z r hr)).add_mem b.property (smoothSobolevData_mem ψ)⟩
  refine ⟨u, fun x => phi x + ψ x, ?_, ?_, ?_, rfl⟩
  · exact (hphi.continuous.add ψ.contDiff.continuous).continuousOn
  · filter_upwards [Lp.coeFn_add b.val.1 (testL2 ψ), hb, testL2_coeFn ψ] with x hadd hbx hψx
    change ((b.val.1 + testL2 ψ : DomainL2 (centeredCube z r hr)) :
      SpatialCoordinates d → ℝ) x = phi x + ψ x
    rw [hadd, Pi.add_apply, hbx, hψx]
  · intro x hx
    have hxnot : x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      have hopen : IsOpen (centeredCube z r hr : Set (SpatialCoordinates d)) :=
        (centeredCube z r hr).isOpen
      rw [hopen.frontier_eq] at hx
      exact hx.2
    have hψ0 : ψ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hxnot (ψ.tsupport_subset h))
    simp only [hψ0, add_zero]

/-- The killed minimizer correction is approximated by smooth compactly supported data, so
the Sobolev response is a limit of energies of continuous-boundary competitors. -/
theorem aux_prop_as_dirichlet_approx
    {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0,
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient
            (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr))
    (phi : SpatialCoordinates d → ℝ)
    (hphi : ContDiff ℝ ∞ phi)
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi) :
    ∃ E : ℕ → ℝ,
      (∀ n, E n ∈ {e : ℝ | ∃ (u : weakSobolevGraph (centeredCube z r hr))
          (U : SpatialCoordinates d → ℝ),
        ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
        ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
          U x = phi x) ∧
        e = sobolevCoefficientForm a u.val u.val}) ∧
      Tendsto E atTop (𝓝 (dirichletResponse (killedResponseSpace hP) a b)) := by
  have hmem : (dirichletMinimizer (killedResponseSpace hP) a b).val - b.val ∈
      killedSobolevGraph (centeredCube z r hr) :=
    dirichletMinimizer_mem_affine (killedResponseSpace hP) a b
  have hcl : (dirichletMinimizer (killedResponseSpace hP) a b).val - b.val ∈ closure
      ((LinearMap.range (smoothSobolevDataLinear (Ω := centeredCube z r hr)) :
        Submodule ℝ (SobolevData (centeredCube z r hr))) :
          Set (SobolevData (centeredCube z r hr))) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hmem
  have hseq := mem_closure_iff_seq_limit.mp hcl
  obtain ⟨x, hxmem, hxlim⟩ := hseq
  choose ψ hψ using hxmem
  refine ⟨fun n => sobolevCoefficientForm a (b.val + smoothSobolevData (ψ n))
      (b.val + smoothSobolevData (ψ n)),
    fun n => aux_prop_as_dirichlet_smooth_competitor z r hr a b phi hphi hb (ψ n), ?_⟩
  have hψ' : ∀ n, smoothSobolevData (ψ n) = x n := hψ
  have hconv : Tendsto (fun n => b.val + smoothSobolevData (ψ n)) atTop
      (𝓝 (dirichletMinimizer (killedResponseSpace hP) a b).val) := by
    have h1 : Tendsto (fun n => b.val + x n) atTop
        (𝓝 (b.val + ((dirichletMinimizer (killedResponseSpace hP) a b).val - b.val))) :=
      tendsto_const_nhds.add hxlim
    rw [add_sub_cancel] at h1
    simpa only [hψ'] using h1
  have hform : Continuous (fun u : SobolevData (centeredCube z r hr) =>
      sobolevCoefficientForm a u u) :=
    (sobolevCoefficientForm a).continuous₂.comp (continuous_id.prodMk continuous_id)
  exact (hform.tendsto _).comp hconv

/-- The Sobolev Dirichlet response equals the continuous-boundary infimum for every
smooth datum: the lower bound is `aux_prop_as_dirichlet_lower_bound`; the upper bound
approximates the killed minimizer correction by smooth compactly supported data, which is
the definition of the killed graph. -/
theorem aux_prop_as_dirichlet_bridge
    {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0,
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient
            (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr))
    (phi : SpatialCoordinates d → ℝ)
    (hphi : ContDiff ℝ ∞ phi)
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi) :
    dirichletResponse (killedResponseSpace hP) a b =
      sInf {e : ℝ | ∃ (u : weakSobolevGraph (centeredCube z r hr))
          (U : SpatialCoordinates d → ℝ),
        ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
        ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
          U x = phi x) ∧
        e = sobolevCoefficientForm a u.val u.val} := by
  have happrox := aux_prop_as_dirichlet_approx z r hr hP a b phi hphi hb
  obtain ⟨E, hE, hElim⟩ := happrox
  have hlow : ∀ e ∈ {e : ℝ | ∃ (u : weakSobolevGraph (centeredCube z r hr))
          (U : SpatialCoordinates d → ℝ),
        ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
        ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
          U x = phi x) ∧
        e = sobolevCoefficientForm a u.val u.val},
      dirichletResponse (killedResponseSpace hP) a b ≤ e := by
    rintro e ⟨u, U, hU, huU, hbdry, he⟩
    exact aux_prop_as_dirichlet_lower_bound hd z r hr hP a b phi hphi hb u U hU huU hbdry e he
  exact le_antisymm (le_csInf ⟨_, hE 0⟩ hlow)
    (ge_of_tendsto' hElim fun n => csInf_le ⟨_, hlow⟩ (hE n))

/-- The global log-potential of the cutoff coefficient, as a continuous field. -/
def aux_prop_as_dirichlet_global_log {d : ℕ}
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ)
    (omega : BilateralField d) : C(SpatialCoordinates d, ℝ) :=
  ContinuousMap.const _ (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) -
    ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) +
    (H omega + ∑ i ∈ Finset.range (N + 1), omega (-(Int.ofNat i)))

theorem aux_prop_as_dirichlet_global_log_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ) :
    Measurable (aux_prop_as_dirichlet_global_log model H N) :=
  measurable_const.add
    (hH.add (Finset.measurable_sum _ fun i _ => measurable_pi_apply (-(Int.ofNat i))))

theorem aux_prop_as_dirichlet_coeff_eq {d : ℕ}
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ)
    (omega : BilateralField d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    haveI : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
      ⟨centeredCube_subset_closedCube z hr⟩
    cutoffPositiveCoefficient model H omega N z hr =
      expPotentialCoefficient (compactPotentialToLp (closedCube z r hr)
        ((aux_prop_as_dirichlet_global_log model H N omega).restrict
          (closedCube z r hr : Set (SpatialCoordinates d)))) := by
  have : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  unfold cutoffPositiveCoefficient normalizedContinuousPositiveCoefficient
  congr 2
  ext x
  simp only [continuousPositiveLog, aux_prop_as_dirichlet_global_log, cutoffCoefficientCM,
    ContinuousMap.coe_mk, ContinuousMap.sub_apply, ContinuousMap.const_apply, Real.log_one,
    sub_zero]
  rw [cutoffCoefficient, Real.log_mul
    (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N).ne')
    (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
  simp only [cutoffPotential]
  have heq : ((aux_prop_as_dirichlet_global_log model H N omega).restrict
      (closedCube z r hr : Set (SpatialCoordinates d))) x =
      (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) -
        ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) +
        (H omega x + ∑ i ∈ Finset.range (N + 1), omega (-(Int.ofNat i)) x) := by
    simp only [aux_prop_as_dirichlet_global_log, ContinuousMap.restrict_apply,
      ContinuousMap.add_apply, ContinuousMap.const_apply, ContinuousMap.sum_apply]
  erw [heq]
  ring

/-- The actual Sobolev Dirichlet response of the cutoff coefficient is measurable in the
field, for every cube, infrared field, Poincare witness and boundary datum. -/
theorem aux_prop_as_dirichlet_response_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0,
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient
            (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr)) :
    Measurable (fun omega => dirichletResponse (killedResponseSpace hP)
      (cutoffPositiveCoefficient model H omega N z hr) b) := by
  have : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have hD := ((continuous_dirichletResponse_compact (killedResponseSpace hP)
    (closedCube z r hr) b).comp
    (ContinuousMap.continuous_restrict (closedCube z r hr : Set (SpatialCoordinates d)))).measurable.comp
      (aux_prop_as_dirichlet_global_log_measurable model H hH N)
  convert hD using 1
  funext omega
  simp only [Function.comp_apply]
  rw [aux_prop_as_dirichlet_coeff_eq model H N omega z hr]

/-- Every smooth datum lies in the Hölder boundary class of every cell, for `0 < beta ≤ 1`. -/
theorem aux_prop_as_dirichlet_smooth_class {d : ℕ}
    (beta : ℝ) (hbeta1 : beta ≤ 1)
    (z : SpatialCoordinates d) (r : ℝ)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi) :
    IsCellBoundaryClass beta z r phi := by
  set G : SpatialCoordinates d → ℝ := rescaledDatum z r phi with hG
  have hGsmooth : ContDiff ℝ 1 G := by
    have haff : ContDiff ℝ 1 (fun y : SpatialCoordinates d => fun i => z i + r * y i) := by
      apply contDiff_pi.2
      intro i
      exact contDiff_const.add (contDiff_const.mul (contDiff_apply ℝ ℝ i))
    exact (hphi.of_le (by exact_mod_cast le_top)).comp haff
  set B : Set (SpatialCoordinates d) := closedBall (0 : SpatialCoordinates d) (1 / 2) with hB
  have hSB : frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)) ⊆ B := by
    refine frontier_subset_closure.trans ?_
    change closure (ball (0 : SpatialCoordinates d) (1 / 2)) ⊆ B
    exact closure_ball_subset_closedBall
  have hBcpt : IsCompact B := isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hBcpt.exists_bound_of_continuousOn
    ((hGsmooth.continuous_fderiv (by norm_num)).continuousOn (s := B))
  have hLip : ∀ x ∈ B, ∀ y ∈ B, |G x - G y| ≤ C * dist x y := by
    intro x hx y hy
    have h := (convex_closedBall (0 : SpatialCoordinates d) (1 / 2)).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => hGsmooth.differentiable (by norm_num) w) (fun w hw => hC w hw) hy hx
    rw [Real.norm_eq_abs, ← dist_eq_norm] at h
    exact h
  have hdist_le : ∀ x y : SpatialCoordinates d,
      dist x y ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
    intro x y
    refine (dist_pi_le_iff (Real.sqrt_nonneg _)).2 fun j => ?_
    rw [Real.dist_eq, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => (x j - y j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ j))
  have heucl_le : ∀ x ∈ B, ∀ y ∈ B,
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d := by
    intro x hx y hy
    apply Real.sqrt_le_sqrt
    have hxy : dist x y ≤ 1 := by
      calc dist x y ≤ dist x 0 + dist y 0 := dist_triangle_right x y 0
        _ ≤ 1 / 2 + 1 / 2 := add_le_add (mem_closedBall.1 hx) (mem_closedBall.1 hy)
        _ = 1 := by norm_num
    calc ∑ j : Fin d, (x j - y j) ^ 2 ≤ ∑ _j : Fin d, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          have hj : |x j - y j| ≤ 1 := by
            have := (dist_le_pi_dist x y j).trans hxy
            rwa [Real.dist_eq] at this
          have h0 : 0 ≤ |x j - y j| := abs_nonneg _
          calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
            _ ≤ 1 ^ 2 := pow_le_pow_left₀ h0 hj 2
            _ = 1 := one_pow 2
      _ = d := by simp
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (mem_closedBall_self (by norm_num)))
  constructor
  · refine ⟨C * (Real.sqrt d) ^ (1 - beta), ?_⟩
    rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    set e := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) with he
    have hdpos : 0 < dist x y := dist_pos.2 hxy
    have hepos : 0 < e := hdpos.trans_le (hdist_le x y)
    have hnum : |G x - G y| ≤ C * e :=
      (hLip x (hSB hx) y (hSB hy)).trans (mul_le_mul_of_nonneg_left (hdist_le x y) hC0)
    have hepow : 0 < e ^ beta := Real.rpow_pos_of_pos hepos beta
    calc |G x - G y| / e ^ beta ≤ C * e / e ^ beta :=
          div_le_div_of_nonneg_right hnum hepow.le
      _ = C * e ^ (1 - beta) := by
          rw [Real.rpow_sub hepos, Real.rpow_one, mul_div_assoc]
      _ ≤ C * (Real.sqrt d) ^ (1 - beta) := by
          apply mul_le_mul_of_nonneg_left _ hC0
          exact Real.rpow_le_rpow hepos.le (heucl_le x (hSB hx) y (hSB hy)) (by linarith)
  · obtain ⟨M, hM⟩ := hBcpt.exists_bound_of_continuousOn hGsmooth.continuous.continuousOn
    refine ⟨M, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    simpa [Real.norm_eq_abs] using hM x (hSB hx)

/-- A convergence-in-measure limit of measurable real functions has a measurable version. -/
theorem aux_prop_as_dirichlet_measurable_version {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ) (hf : ∀ n, Measurable (f n)) (g : Ω → ℝ)
    (h : TendstoInMeasure μ f atTop g) :
    ∃ g' : Ω → ℝ, Measurable g' ∧ g' =ᵐ[μ] g := by
  obtain ⟨ns, -, hae⟩ := h.exists_seq_tendsto_ae
  have hg : AEMeasurable g μ :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hf (ns n)).aemeasurable) hae
  exact ⟨hg.mk g, hg.measurable_mk, hg.ae_eq_mk.symm⟩

/-- Pointwise two-sided comparison: finite two-cutoff comparisons at `N` and `M`, with `M`
close to the limit, give the relative-plus-additive bound at `N`. -/
theorem aux_prop_as_dirichlet_pointwise
    (x y L q err δ c0 A : ℝ) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hqc : q - 1 ≤ c0)
    (herr : 0 ≤ err) (hδ : 0 < δ) (hA : 2 * δ + err ≤ A)
    (hL : 0 ≤ L) (hxy : x ≤ q * y + err) (hyx : y ≤ q * x + err) (hyL : |y - L| < δ) :
    |x - L| ≤ c0 * L + A := by
  have hyL' := abs_sub_lt_iff.1 hyL
  have hq0 : 0 ≤ q := by linarith
  have h1 : (q - 1) * L ≤ c0 * L := mul_le_mul_of_nonneg_right hqc hL
  have h2 : q * y ≤ q * (L + δ) := mul_le_mul_of_nonneg_left (by linarith) hq0
  have h3 : q * δ ≤ 2 * δ := mul_le_mul_of_nonneg_right hq2 hδ.le
  rw [abs_le]
  constructor
  · by_cases hxL : L ≤ x
    · have hc0 : 0 ≤ c0 := by linarith
      have : 0 ≤ c0 * L := mul_nonneg hc0 hL
      linarith
    · push Not at hxL
      have h4 : (q - 1) * x ≤ (q - 1) * L :=
        mul_le_mul_of_nonneg_left hxL.le (by linarith)
      linarith
  · linarith

/-- Sending the second cutoff to infinity in the finite comparisons. -/
theorem aux_prop_as_dirichlet_limit_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Lam : ℕ → Ω → ℝ) (LamE : Ω → ℝ)
    (hconv : TendstoInMeasure μ Lam atTop LamE) (hnn : ∀ᵐ om ∂μ, 0 ≤ LamE om)
    (N : ℕ) (q err δ c0 A : ℝ) (p : ℝ≥0∞)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hqc : q - 1 ≤ c0)
    (herr : 0 ≤ err) (hδ : 0 < δ) (hA : 2 * δ + err ≤ A)
    (hbad : ∀ᶠ M in atTop, ∃ Bad1 Bad2 : Set Ω, μ Bad1 + μ Bad2 ≤ p ∧
      (∀ om ∉ Bad1, Lam N om ≤ q * Lam M om + err) ∧
      (∀ om ∉ Bad2, Lam M om ≤ q * Lam N om + err)) :
    μ {om | c0 * LamE om + A < |Lam N om - LamE om|} ≤ p := by
  set T := {om | c0 * LamE om + A < |Lam N om - LamE om|} with hT
  have hneg : μ {om | LamE om < 0} = 0 := by
    simpa only [not_le] using ae_iff.1 hnn
  have hle : ∀ᶠ M in atTop, μ T ≤ p + μ {om | δ ≤ dist (Lam M om) (LamE om)} := by
    filter_upwards [hbad] with M hM
    obtain ⟨Bad1, Bad2, hp, h1, h2⟩ := hM
    have hsub : T ⊆ (Bad1 ∪ Bad2) ∪ ({om | δ ≤ dist (Lam M om) (LamE om)} ∪ {om | LamE om < 0}) := by
      intro om hom
      by_contra hcon
      simp only [Set.mem_union, not_or, mem_ofPred_eq, not_le, not_lt] at hcon
      obtain ⟨⟨hb1, hb2⟩, hd, hL⟩ := hcon
      have hdist : |Lam M om - LamE om| < δ := by rwa [Real.dist_eq] at hd
      have := aux_prop_as_dirichlet_pointwise (Lam N om) (Lam M om) (LamE om) q err δ c0 A
        hq1 hq2 hqc herr hδ hA hL (h1 om hb1) (h2 om hb2) hdist
      exact (not_lt.2 this) hom
    calc μ T ≤ μ ((Bad1 ∪ Bad2) ∪ ({om | δ ≤ dist (Lam M om) (LamE om)} ∪ {om | LamE om < 0})) :=
          measure_mono hsub
      _ ≤ μ (Bad1 ∪ Bad2) + μ ({om | δ ≤ dist (Lam M om) (LamE om)} ∪ {om | LamE om < 0}) :=
          measure_union_le _ _
      _ ≤ (μ Bad1 + μ Bad2) + (μ {om | δ ≤ dist (Lam M om) (LamE om)} + μ {om | LamE om < 0}) :=
          add_le_add (measure_union_le _ _) (measure_union_le _ _)
      _ = (μ Bad1 + μ Bad2) + μ {om | δ ≤ dist (Lam M om) (LamE om)} := by rw [hneg, add_zero]
      _ ≤ p + μ {om | δ ≤ dist (Lam M om) (LamE om)} := add_le_add hp le_rfl
  have hlim : Tendsto (fun M => p + μ {om | δ ≤ dist (Lam M om) (LamE om)}) atTop (𝓝 (p + 0)) :=
    tendsto_const_nhds.add ((tendstoInMeasure_iff_dist.mp hconv) δ hδ)
  rw [add_zero] at hlim
  exact ge_of_tendsto hlim hle

/-- The exponential tail sequence is summable. -/
theorem aux_prop_as_dirichlet_tail_summable (Ce ce : ℝ) (hce : 0 < ce) :
    Summable (fun N : ℕ => Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) := by
  have hr0 : 0 ≤ (3 : ℝ) ^ (-ce) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-ce) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeo := (summable_geometric_of_lt_one hr0 hr1).mul_left Ce
  convert hgeo using 2 with N
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), neg_mul]

/-- Borel--Cantelli from a summable relative-plus-additive tail, for every relative
tolerance, gives almost-sure convergence along the full sequence. -/
theorem aux_prop_as_dirichlet_ae_of_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (Cg : ℝ)
    (htail : ∀ eps : ℝ, 0 < eps →
      ∃ (Ce ce : ℝ), ∃ Ne : ℕ, 0 < Ce ∧ 0 < ce ∧
        ∀ N : ℕ, Ne ≤ N →
          μ {om | Cg * eps * g om + Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) < |f N om - g om|} ≤
            ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) :
    ∀ᵐ om ∂μ, Tendsto (fun N => f N om) atTop (𝓝 (g om)) := by
  have hj : ∀ j : ℕ, ∃ (Ce ce : ℝ), 0 < Ce ∧ 0 < ce ∧ ∀ᵐ om ∂μ, ∀ᶠ N in atTop,
      |f N om - g om| ≤ Cg * (1 / ((j : ℝ) + 1)) * g om + Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) := by
    intro j
    obtain ⟨Ce, ce, Ne, hCe, hce, hN⟩ := htail (1 / ((j : ℝ) + 1)) (by positivity)
    refine ⟨Ce, ce, hCe, hce, ?_⟩
    classical
    let s : ℕ → Set Ω := fun N => if Ne ≤ N then
      {om | Cg * (1 / ((j : ℝ) + 1)) * g om + Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) < |f N om - g om|}
      else ∅
    have hs : ∀ N, μ (s N) ≤ ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) := by
      intro N
      by_cases hNe : Ne ≤ N
      · simp only [s, ite_eq_left hNe]
        exact hN N hNe
      · simp only [s, ite_eq_right hNe, measure_empty]
        exact zero_le
    have hsum : ∑' N, μ (s N) ≠ ⊤ := by
      have hnn : ∀ N : ℕ, 0 ≤ Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) := fun N =>
        mul_nonneg hCe.le (Real.rpow_nonneg (by norm_num) _)
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hs)
      rw [← ENNReal.ofReal_tsum_of_nonneg hnn (aux_prop_as_dirichlet_tail_summable Ce ce hce)]
      exact ENNReal.ofReal_ne_top
    filter_upwards [ae_eventually_notMem hsum] with om hom
    filter_upwards [hom, eventually_ge_atTop Ne] with N hN hNe
    simp only [s, ite_eq_left hNe, mem_ofPred_eq, not_lt] at hN
    exact hN
  choose Ce ce hCe hce hae using hj
  filter_upwards [ae_all_iff.2 hae] with om hom
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨j, hjlt⟩ := exists_nat_gt ((|Cg| * |g om| + 1) * 2 / ε)
  have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hrel : |Cg * (1 / ((j : ℝ) + 1)) * g om| < ε / 2 := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1))]
    have hA : 0 ≤ |Cg| * |g om| := by positivity
    rw [mul_comm |Cg| _, mul_assoc, one_div, inv_mul_eq_div, div_lt_iff₀ hjpos]
    have : (|Cg| * |g om| + 1) * 2 < ε * ((j : ℝ) + 1) := by
      rw [div_lt_iff₀ hε] at hjlt
      linarith
    nlinarith
  have hpow : Tendsto (fun N : ℕ => Ce j * (3 : ℝ) ^ (-(ce j * (N : ℝ)))) atTop (𝓝 0) :=
    (aux_prop_as_dirichlet_tail_summable (Ce j) (ce j) (hce j)).tendsto_atTop_zero
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.1 hpow) (ε / 2) (by positivity)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 (hom j)
  refine ⟨max N1 N2, fun N hN => ?_⟩
  have h1 := hN1 N (le_of_max_le_left hN)
  have h2 := hN2 N (le_of_max_le_right hN)
  rw [Real.dist_eq, sub_zero] at h1
  rw [Real.dist_eq]
  have hrel' := (abs_lt.1 hrel).2
  have h1' := (abs_lt.1 h1).2
  linarith

/-- The normalization sequence `κ_J` of the finite-stopping comparison. -/
def aux_prop_as_dirichlet_kap {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (J : ℕ) : ℝ :=
  Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
    SubdiffusiveProcess.CoarseGrainingVocab.ahom model J

theorem aux_prop_as_dirichlet_kap_pos {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (J : ℕ) : 0 < aux_prop_as_dirichlet_kap model J :=
  mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model J)

/-- The finite two-cutoff comparisons of `lem_finite_stopping` at one fixed model, infrared
field, cube, tolerance `eta` and constants `Ceta, gamma, N0`. -/
def aux_prop_as_dirichlet_FS_at {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (theta : ℝ) (H1 : ℕ) (Dgeom Cgeom eta Ceta gamma : ℝ) (N0 : ℕ) : Prop :=
      ∀ (N M : ℕ), N0 ≤ N → N ≤ M →
      ∀ (c : ℝ), 0 < c → c ≤ 2 →
      ∀ (S : ℕ → Prop),
        theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
          (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) →
      ((∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
          (aux_prop_as_dirichlet_kap model (N - H1 * n) / aux_prop_as_dirichlet_kap model N) /
            (aux_prop_as_dirichlet_kap model (M - H1 * n) / aux_prop_as_dirichlet_kap model M)
              ≤ c) →
        ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖@subspaceGradient d (centeredCube z r hr)
              (killedSobolevGraph (centeredCube z r hr)) u‖,
        ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi →
        ∀ b : weakSobolevGraph (centeredCube z r hr),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
        ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
          (chaosSampleLaw model).toMeasure Bad ≤
            ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
          ∀ omega ∉ Bad,
          dirichletResponse (killedResponseSpace hP)
              (cutoffPositiveCoefficient model H omega N z hr) b ≤
            c * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom) *
              dirichletResponse (killedResponseSpace hP)
                (cutoffPositiveCoefficient model H omega M z hr) b +
            Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * (c2Norm (closedCube z r hr) phi) ^ 2) ∧
      ((∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
          (aux_prop_as_dirichlet_kap model (M - H1 * n) / aux_prop_as_dirichlet_kap model M) /
            (aux_prop_as_dirichlet_kap model (N - H1 * n) / aux_prop_as_dirichlet_kap model N)
              ≤ c) →
        ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖@subspaceGradient d (centeredCube z r hr)
              (killedSobolevGraph (centeredCube z r hr)) u‖,
        ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi →
        ∀ b : weakSobolevGraph (centeredCube z r hr),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
        ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
          (chaosSampleLaw model).toMeasure Bad ≤
            ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
          ∀ omega ∉ Bad,
          dirichletResponse (killedResponseSpace hP)
              (cutoffPositiveCoefficient model H omega M z hr) b ≤
            c * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom) *
              dirichletResponse (killedResponseSpace hP)
                (cutoffPositiveCoefficient model H omega N z hr) b +
            Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * (c2Norm (closedCube z r hr) phi) ^ 2)

/-- The conclusion of `lem_finite_stopping` at one fixed model, infrared field and cube. -/
def aux_prop_as_dirichlet_FS {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (theta : ℝ) (H1 : ℕ) (Dgeom Cgeom : ℝ) : Prop :=
  ∀ (eta : ℝ), 0 < eta →
      ∃ (Ceta gamma : ℝ) (N0 : ℕ), 0 < Ceta ∧ 0 < gamma ∧
        aux_prop_as_dirichlet_FS_at model H z r hr theta H1 Dgeom Cgeom eta Ceta gamma N0

/-- `lem_finite_stopping` delivers the packaged conclusion at every admissible cube. -/
theorem aux_prop_as_dirichlet_FS_of_lem {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d ⟨by omega⟩)
    (Dbase : @sum_errors_baseline_input d ⟨by omega⟩ _ _)
    (_Interp : CubeFractionalInterpolationInput d hd)
    (theta : ℝ) (htheta : 0 < theta) :
    ∃ (H1 : ℕ) (Dgeom Cgeom delta0 : ℝ),
      0 < H1 ∧ 0 < Dgeom ∧ 0 < Cgeom ∧ 0 < delta0 ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_hH : InfraredCharacterization model H) (_hsmall : model.delta ≤ delta0)
        (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (_htriadic : ∃ j : ℤ, r = (3 : ℝ) ^ j),
        aux_prop_as_dirichlet_FS model H z r hr theta H1 Dgeom Cgeom := by
  obtain ⟨H1, Dgeom, Cgeom, delta0, hH1, hDgeom, hCgeom, hdelta0, hFS⟩ :=
    lem_finite_stopping d hd Jc Pc Xc Sf W Cp Step D hES Dbase theta htheta
  exact ⟨H1, Dgeom, Cgeom, delta0, hH1, hDgeom, hCgeom, hdelta0,
    fun model Rm Sreg It H hH hsmall z r hr htriadic =>
      hFS model Rm Sreg It H hH hsmall z r hr htriadic⟩



def aux_prop_as_dirichlet_Bmin {d : ℕ}
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (N : ℕ) (omega : BilateralField d) (g : SpatialCoordinates d → ℝ) : ℝ :=
  sInf {e : ℝ | ∃ (u : weakSobolevGraph (centeredCube z r hr))
      (U : SpatialCoordinates d → ℝ),
    ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
    ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
    (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      U x = g x) ∧
    e = sobolevCoefficientForm
      (cutoffPositiveCoefficient model H omega N z hr) u.val u.val}

/-- The unit cube carries the standard killed Poincare inequality. -/
theorem aux_prop_as_dirichlet_unit_poincare {d : ℕ} (hd : 2 ≤ d) :
    ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) w‖ := by
  have : NeZero d := ⟨by omega⟩
  have hgeom : Homogenization.IsOpenBoundedConvexDomain
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
    refine ⟨(centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen, ⟨1, one_pos, ?_⟩, ?_⟩
    · intro x hx i
      have hx' : dist x 0 < 1 / 2 := hx
      have hi : |x i| ≤ dist x 0 := by
        have := dist_le_pi_dist x 0 i
        simpa [Real.dist_eq] using this
      linarith
    · exact convex_ball (0 : SpatialCoordinates d) (1 / 2)
  exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
    (centeredCube (0 : SpatialCoordinates d) 1 one_pos) hgeom).1

/-- The working-level density from `working_levels_ratio`, instantiated with the actual
Sobolev response of a fixed nonconstant affine datum on the unit cube. -/
theorem aux_prop_as_dirichlet_window {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (beta : ℝ) (hbeta_upper : beta < 1)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHm : Measurable H)
    (e : ℕ → ℝ)
    (he : ∀ k : ℕ, 0 < e k ∧ Tendsto (fun N => aux_prop_as_dirichlet_kap model (N - k) /
      aux_prop_as_dirichlet_kap model N) atTop (𝓝 (e k)))
    (RL0 : BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ))
    (hRL0 : ∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta 0 1 g →
      TendstoInMeasure (chaosSampleLaw model).toMeasure
        (fun N omega => aux_prop_as_dirichlet_Bmin model H 0 1 one_pos N omega g) atTop
        (fun omega => (RL0 omega g) ^ 2))
    (hpos0 : ∀ p : Fin d → ℝ, p ≠ 0 →
      ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
        0 < (RL0 omega (fun x : SpatialCoordinates d => ∑ i : Fin d, p i * x i)) ^ 2)
    (H1 : ℕ) (hH1 : 0 < H1) (Dgeom Cgeom : ℝ) (hCgeom : 0 < Cgeom)
    (hFS0 : aux_prop_as_dirichlet_FS model H 0 1 one_pos (1 / 8) H1 Dgeom Cgeom) :
    ∀ eps : ℝ, 0 < eps →
      ∃ Ne : ℕ, ∀ N : ℕ, Ne ≤ N →
        (1 - 2 * (1 / 8 : ℝ)) *
            (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ)
          < (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧
              |(aux_prop_as_dirichlet_kap model (N - H1 * n) / aux_prop_as_dirichlet_kap model N) /
                e (H1 * n) - 1| ≤ eps} : ℝ) := by
  set P := (chaosSampleLaw model).toMeasure with hPdef
  have hP0 := aux_prop_as_dirichlet_unit_poincare hd
  let i0 : Fin d := ⟨0, by omega⟩
  let p0 : Fin d → ℝ := Pi.single i0 1
  have hp0 : p0 ≠ 0 := by
    intro h
    have := congrFun h i0
    simp [p0] at this
  let phi0 : SpatialCoordinates d → ℝ := fun x => ∑ i : Fin d, p0 i * x i
  have hphi0eq : phi0 = fun x => affineSlope p0 x := by
    funext x
    rw [affineSlope_apply]
  have hphi0 : ContDiff ℝ ∞ phi0 := by
    rw [hphi0eq]
    exact (affineSlope p0).contDiff
  let b0 : weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos) :=
    affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) p0 0
  have hb0 : ((b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 :
      SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))] phi0 := by
    filter_upwards [affineL2_coeFn (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
      p0 0] with x hx
    change (affineL2 (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) p0 0 :
      SpatialCoordinates d → ℝ) x = phi0 x
    rw [hx, add_zero, hphi0eq]
  let Lam0 : ℕ → BilateralField d → ℝ := fun N omega =>
    dirichletResponse (killedResponseSpace hP0)
      (cutoffPositiveCoefficient model H omega N (0 : SpatialCoordinates d) one_pos) b0
  have hmeas0 : ∀ N, Measurable (Lam0 N) := fun N =>
    aux_prop_as_dirichlet_response_measurable model H hHm N 0 1 one_pos hP0 b0
  have hbridge0 : Lam0 = fun N omega => aux_prop_as_dirichlet_Bmin model H 0 1 one_pos N omega phi0 := by
    funext N omega
    exact aux_prop_as_dirichlet_bridge hd 0 1 one_pos hP0 _ b0 phi0 hphi0 hb0
  have hconv0 : TendstoInMeasure P Lam0 atTop (fun omega => (RL0 omega phi0) ^ 2) := by
    rw [hbridge0]
    exact hRL0 phi0 (aux_prop_as_dirichlet_smooth_class beta hbeta_upper.le 0 1 phi0 hphi0)
  obtain ⟨LamE0, hLamE0m, hLamE0ae⟩ :=
    aux_prop_as_dirichlet_measurable_version P Lam0 hmeas0 _ hconv0
  have hLamE0pos : ∀ᵐ omega ∂P, 0 < LamE0 omega := by
    filter_upwards [hLamE0ae, hpos0 p0 hp0] with omega h1 h2
    rw [h1]
    exact h2
  have hLamconv0 : TendstoInMeasure P Lam0 atTop LamE0 := hconv0.congr_right hLamE0ae.symm
  have hfinite : ∀ eta : ℝ, 0 < eta →
      ∃ (Ceta gamma : ℝ) (N0 : ℕ), 0 < Ceta ∧ 0 < gamma ∧
      ∀ (N M : ℕ), N0 ≤ N → N ≤ M →
      ∀ (c : ℝ), 0 < c → c ≤ 2 →
      ∀ (S : Finset ℕ),
        (1 / 8 : ℝ) * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ)
          ≤ (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ n ∈ S} : ℝ) →
        ((∀ n : ℕ, n ∈ S → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
            (aux_prop_as_dirichlet_kap model (N - H1 * n) / aux_prop_as_dirichlet_kap model N) /
              (aux_prop_as_dirichlet_kap model (M - H1 * n) / aux_prop_as_dirichlet_kap model M)
                ≤ c) →
          P {om | c * (1 + (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) * eta) * Lam0 M om +
              Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) < Lam0 N om}
            ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)))) ∧
        ((∀ n : ℕ, n ∈ S → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
            (aux_prop_as_dirichlet_kap model (M - H1 * n) / aux_prop_as_dirichlet_kap model M) /
              (aux_prop_as_dirichlet_kap model (N - H1 * n) / aux_prop_as_dirichlet_kap model N)
                ≤ c) →
          P {om | c * (1 + (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) * eta) * Lam0 N om +
              Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) < Lam0 M om}
            ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)))) := by
    intro eta heta
    obtain ⟨Ceta, gamma, N0, hCeta, hgamma, hN⟩ := hFS0 eta heta
    set c2 := c2Norm (closedCube (0 : SpatialCoordinates d) 1 one_pos) phi0 with hc2
    refine ⟨Ceta * (1 + c2 ^ 2), gamma, N0, by positivity, hgamma, ?_⟩
    intro N M hN0 hNM c hc0 hc2' S hfrac
    have hcard : (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ n ∈ S} : ℝ) =
        (Nat.card {n : ℕ // n ∈ S ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) := by
      congr 1
      exact Nat.card_congr (Equiv.subtypeEquivRight fun n =>
        ⟨fun h => ⟨h.2.2, h.1, h.2.1⟩, fun h => ⟨h.2.1, h.2.2, h.1⟩⟩)
    rw [hcard] at hfrac
    obtain ⟨h1, h2⟩ := hN N M hN0 hNM c hc0 hc2' (fun n => n ∈ S) hfrac
    have hpow0 : 0 ≤ Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) :=
      mul_nonneg hCeta.le (Real.rpow_nonneg (by norm_num) _)
    have herr : Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * c2 ^ 2 ≤
        Ceta * (1 + c2 ^ 2) * (3 : ℝ) ^ (-gamma * (N : ℝ)) := by
      nlinarith [hpow0]
    have hofr : ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) ≤
        ENNReal.ofReal (Ceta * (1 + c2 ^ 2) * (3 : ℝ) ^ (-gamma * (N : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [hpow0, sq_nonneg c2]
    have hcoef : c * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom) =
        c * (1 + (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) * eta) := by ring
    constructor
    · intro hyp
      obtain ⟨Bad, -, hBad, hgood⟩ := h1 hyp hP0 phi0 hphi0 b0 hb0
      refine le_trans (measure_mono ?_) (hBad.trans hofr)
      intro om hom
      by_contra hnot
      have hg := hgood om hnot
      rw [hcoef] at hg
      have hom' : c * (1 + (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) * eta) * Lam0 M om +
          Ceta * (1 + c2 ^ 2) * (3 : ℝ) ^ (-gamma * (N : ℝ)) < Lam0 N om := hom
      change Lam0 N om ≤ c * (1 + (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) * eta) * Lam0 M om +
        Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * c2 ^ 2 at hg
      linarith
    · intro hyp
      obtain ⟨Bad, -, hBad, hgood⟩ := h2 hyp hP0 phi0 hphi0 b0 hb0
      refine le_trans (measure_mono ?_) (hBad.trans hofr)
      intro om hom
      by_contra hnot
      have hg := hgood om hnot
      rw [hcoef] at hg
      have hom' : c * (1 + (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) * eta) * Lam0 N om +
          Ceta * (1 + c2 ^ 2) * (3 : ℝ) ^ (-gamma * (N : ℝ)) < Lam0 M om := hom
      change Lam0 M om ≤ c * (1 + (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) * eta) * Lam0 N om +
        Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * c2 ^ 2 at hg
      linarith
  exact working_levels_ratio (BilateralField d) P (aux_prop_as_dirichlet_kap model) e
    (aux_prop_as_dirichlet_kap_pos model) (fun k => (he k).1) (fun k => (he k).2)
    (1 / 8) (by norm_num) (by norm_num) H1 hH1 (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) (by positivity)
    Lam0 LamE0 hmeas0 hLamE0m hLamE0pos hLamconv0 hfinite

/-- Elementary bounds for the comparison factor `q = c (1 + t)`. -/
theorem aux_prop_as_dirichlet_q_bounds (e0 t : ℝ) (he0 : 0 < e0) (he1 : e0 ≤ 1)
    (ht0 : 0 ≤ t) (ht : t ≤ e0 / 3) :
    0 < (1 + e0 / 8) / (1 - e0 / 8) ∧ (1 + e0 / 8) / (1 - e0 / 8) ≤ 2 ∧
      1 ≤ (1 + e0 / 8) / (1 - e0 / 8) * (1 + t) ∧
      (1 + e0 / 8) / (1 - e0 / 8) * (1 + t) ≤ 2 ∧
      (1 + e0 / 8) / (1 - e0 / 8) * (1 + t) - 1 ≤ e0 := by
  have hden : 0 < 1 - e0 / 8 := by linarith
  have hc1 : 1 ≤ (1 + e0 / 8) / (1 - e0 / 8) := by
    rw [le_div_iff₀ hden]
    linarith
  have hc3 : (1 + e0 / 8) / (1 - e0 / 8) ≤ 1 + e0 / 3 := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hq : (1 + e0 / 8) / (1 - e0 / 8) * (1 + t) ≤ (1 + e0 / 3) * (1 + e0 / 3) :=
    mul_le_mul hc3 (by linarith) (by linarith) (by linarith)
  have hq1 : 1 ≤ (1 + e0 / 8) / (1 - e0 / 8) * (1 + t) := by
    have := mul_le_mul hc1 (by linarith : (1 : ℝ) ≤ 1 + t) zero_le_one (by linarith)
    linarith
  refine ⟨by linarith, by linarith, hq1, by nlinarith, by nlinarith⟩

/-- Ratio control from two relative approximations of the same positive limit. -/
theorem aux_prop_as_dirichlet_ratio_le (a b el eps : ℝ) (hel : 0 < el) (heps : eps < 1)
    (ha : |a / el - 1| ≤ eps) (hb : |b / el - 1| ≤ eps) :
    a / b ≤ (1 + eps) / (1 - eps) := by
  have ha' := abs_le.1 ha
  have hb' := abs_le.1 hb
  have hbpos : 0 < b / el := by linarith
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_div] at hbpos
    exact lt_irrefl _ hbpos
  have heq : a / b = (a / el) / (b / el) := by
    field_simp
  rw [heq]
  exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)

/-- Choice of the finite-stopping tolerance `eta` making the geometric factor small. -/
theorem aux_prop_as_dirichlet_eta_exists (Cgeom Dgeom : ℝ) (H1 : ℕ) (hCgeom : 0 < Cgeom)
    (e0 : ℝ) (he0 : 0 < e0) :
    ∃ eta : ℝ, 0 < eta ∧ Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom ≤ e0 / 3 := by
  have hL : 0 ≤ ((3 : ℝ) ^ H1) ^ Dgeom := Real.rpow_nonneg (pow_nonneg (by norm_num) _) _
  have hG0 : 0 ≤ Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom := mul_nonneg hCgeom.le hL
  refine ⟨e0 / (3 * (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom + 1)), by positivity, ?_⟩
  have hden : 0 < 3 * (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom + 1) := by linarith
  have hteq : Cgeom * (e0 / (3 * (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom + 1))) * ((3 : ℝ) ^ H1) ^ Dgeom =
      e0 / 3 * ((Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) / (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom + 1)) := by
    field_simp
  rw [hteq]
  have h1 : (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) / (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom + 1) ≤ 1 :=
    (div_le_one (by linarith)).2 (by linarith)
  have h3 : 0 ≤ e0 / 3 := by positivity
  calc e0 / 3 * ((Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) / (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom + 1))
      ≤ e0 / 3 * 1 := mul_le_mul_of_nonneg_left h1 h3
    _ = e0 / 3 := mul_one _

/-- For a fixed good level `N`, the two finite comparisons hold outside two small bad events
for every sufficiently large second cutoff `M`. -/
theorem aux_prop_as_dirichlet_bad {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (e : ℕ → ℝ)
    (he : ∀ k : ℕ, 0 < e k ∧ Tendsto (fun N => aux_prop_as_dirichlet_kap model (N - k) /
      aux_prop_as_dirichlet_kap model N) atTop (𝓝 (e k)))
    (H1 : ℕ) (hH1 : 0 < H1) (Dgeom Cgeom eta Ceta gamma : ℝ) (N0 : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hFSN : aux_prop_as_dirichlet_FS_at model H z r hr (1 / 8) H1 Dgeom Cgeom eta Ceta gamma N0)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hc2 : (1 + x) / (1 - x) ≤ 2)
    (N : ℕ) (hN0N : N0 ≤ N)
    (hwinN : (1 - 2 * (1 / 8 : ℝ)) *
            (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ)
          < (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧
              |(aux_prop_as_dirichlet_kap model (N - H1 * n) / aux_prop_as_dirichlet_kap model N) /
                e (H1 * n) - 1| ≤ x} : ℝ))
    (hP : ∃ K : ℝ≥0,
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient
            (killedSobolevGraph (centeredCube z r hr)) w‖)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi) :
    ∀ᶠ M in atTop, ∃ Bad1 Bad2 : Set (BilateralField d),
      (chaosSampleLaw model).toMeasure Bad1 + (chaosSampleLaw model).toMeasure Bad2 ≤
        ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) +
          ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
      (∀ om ∉ Bad1, dirichletResponse (killedResponseSpace hP)
          (cutoffPositiveCoefficient model H om N z hr) b ≤
        (1 + x) / (1 - x) * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom) *
          dirichletResponse (killedResponseSpace hP)
            (cutoffPositiveCoefficient model H om M z hr) b +
        Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * (c2Norm (closedCube z r hr) phi) ^ 2) ∧
      (∀ om ∉ Bad2, dirichletResponse (killedResponseSpace hP)
          (cutoffPositiveCoefficient model H om M z hr) b ≤
        (1 + x) / (1 - x) * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom) *
          dirichletResponse (killedResponseSpace hP)
            (cutoffPositiveCoefficient model H om N z hr) b +
        Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * (c2Norm (closedCube z r hr) phi) ^ 2) := by
  have hc0 : 0 < (1 + x) / (1 - x) := div_pos (by linarith) (by linarith)
  let S : ℕ → Prop := fun n =>
    |(aux_prop_as_dirichlet_kap model (N - H1 * n) / aux_prop_as_dirichlet_kap model N) /
      e (H1 * n) - 1| ≤ x
  have hfrac : (1 / 8 : ℝ) * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
      (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) := by
    have hcard : (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ S n} : ℝ) =
        (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) := by
      congr 1
      exact Nat.card_congr (Equiv.subtypeEquivRight fun n =>
        ⟨fun h => ⟨h.2.2, h.1, h.2.1⟩, fun h => ⟨h.2.1, h.2.2, h.1⟩⟩)
    have h : (1 - 2 * (1 / 8 : ℝ)) *
        (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) <
      (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ S n} : ℝ) := hwinN
    rw [hcard] at h
    have hW : (0 : ℝ) ≤ (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) :=
      Nat.cast_nonneg _
    linarith only [h, hW]
  have hfar : ∀ᶠ M in atTop, ∀ n ∈ Finset.range (N + 1),
      |(aux_prop_as_dirichlet_kap model (M - H1 * n) / aux_prop_as_dirichlet_kap model M) /
        e (H1 * n) - 1| ≤ x := by
    rw [Filter.eventually_all_finset]
    intro n _
    have hlim := ((he (H1 * n)).2).div_const (e (H1 * n))
    rw [div_self (he (H1 * n)).1.ne'] at hlim
    filter_upwards [Metric.tendsto_nhds.1 hlim x hx0] with M hM
    rw [Real.dist_eq] at hM
    exact hM.le
  have hwin_le : ∀ n : ℕ, 4 * (H1 * n) ≤ 3 * N → n ∈ Finset.range (N + 1) := by
    intro n hn
    rw [Finset.mem_range]
    have : n ≤ H1 * n := Nat.le_mul_of_pos_left n hH1
    omega
  filter_upwards [hfar, eventually_ge_atTop N] with M hM hNM
  obtain ⟨h1, h2⟩ := hFSN N M hN0N hNM ((1 + x) / (1 - x)) hc0 hc2 S hfrac
  have hr1 : ∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
      (aux_prop_as_dirichlet_kap model (N - H1 * n) / aux_prop_as_dirichlet_kap model N) /
        (aux_prop_as_dirichlet_kap model (M - H1 * n) / aux_prop_as_dirichlet_kap model M) ≤
          (1 + x) / (1 - x) := by
    intro n hS _ hn2
    exact aux_prop_as_dirichlet_ratio_le _ _ _ x (he (H1 * n)).1 hx1 hS (hM n (hwin_le n hn2))
  have hr2 : ∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
      (aux_prop_as_dirichlet_kap model (M - H1 * n) / aux_prop_as_dirichlet_kap model M) /
        (aux_prop_as_dirichlet_kap model (N - H1 * n) / aux_prop_as_dirichlet_kap model N) ≤
          (1 + x) / (1 - x) := by
    intro n hS _ hn2
    exact aux_prop_as_dirichlet_ratio_le _ _ _ x (he (H1 * n)).1 hx1 (hM n (hwin_le n hn2)) hS
  obtain ⟨Bad1, -, hB1, hg1⟩ := h1 hr1 hP phi hphi b hb
  obtain ⟨Bad2, -, hB2, hg2⟩ := h2 hr2 hP phi hphi b hb
  exact ⟨Bad1, Bad2, add_le_add hB1 hB2, hg1, hg2⟩

/-- The per-cube, per-datum summable tail from the working levels and the two finite
comparisons of `lem_finite_stopping`, with the second cutoff sent to infinity. -/
theorem aux_prop_as_dirichlet_tail {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (e : ℕ → ℝ)
    (he : ∀ k : ℕ, 0 < e k ∧ Tendsto (fun N => aux_prop_as_dirichlet_kap model (N - k) /
      aux_prop_as_dirichlet_kap model N) atTop (𝓝 (e k)))
    (H1 : ℕ) (hH1 : 0 < H1) (Dgeom Cgeom : ℝ) (hCgeom : 0 < Cgeom)
    (hwin : ∀ eps : ℝ, 0 < eps →
      ∃ Ne : ℕ, ∀ N : ℕ, Ne ≤ N →
        (1 - 2 * (1 / 8 : ℝ)) *
            (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ)
          < (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧
              |(aux_prop_as_dirichlet_kap model (N - H1 * n) / aux_prop_as_dirichlet_kap model N) /
                e (H1 * n) - 1| ≤ eps} : ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0,
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient
            (killedSobolevGraph (centeredCube z r hr)) w‖)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (hFSi : aux_prop_as_dirichlet_FS model H z r hr (1 / 8) H1 Dgeom Cgeom)
    (LamE : BilateralField d → ℝ)
    (hconv : TendstoInMeasure (chaosSampleLaw model).toMeasure
      (fun N om => dirichletResponse (killedResponseSpace hP)
        (cutoffPositiveCoefficient model H om N z hr) b) atTop LamE)
    (hnn : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure, 0 ≤ LamE om) :
    ∀ eps : ℝ, 0 < eps →
      ∃ (Ce ce : ℝ), ∃ Ne : ℕ,
        0 < Ce ∧ 0 < ce ∧
          ∀ N : ℕ, Ne ≤ N →
            (chaosSampleLaw model).toMeasure
                {om |
                  1 * eps * LamE om + Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                    |dirichletResponse (killedResponseSpace hP)
                        (cutoffPositiveCoefficient model H om N z hr) b - LamE om|} ≤
              ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) := by
  intro eps heps
  obtain ⟨e0, he0, he0e, he01⟩ : ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ eps ∧ e0 ≤ 1 :=
    ⟨min eps 1, lt_min heps one_pos, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨eta, heta0, htle⟩ := aux_prop_as_dirichlet_eta_exists Cgeom Dgeom H1 hCgeom e0 he0
  have ht0 : 0 ≤ Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom :=
    mul_nonneg (mul_nonneg hCgeom.le heta0.le)
      (Real.rpow_nonneg (pow_nonneg (by norm_num) _) _)
  obtain ⟨_, hc2, hq1, hq2, hqe⟩ :=
    aux_prop_as_dirichlet_q_bounds e0 (Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom) he0 he01 ht0 htle
  have hx0 : 0 < e0 / 8 := by linarith only [he0]
  have hx1 : e0 / 8 < 1 := by linarith only [he01]
  obtain ⟨Ne1, hNe1⟩ := hwin (e0 / 8) hx0
  obtain ⟨Ceta, gamma, N0, hCeta, hgamma, hFSN⟩ := hFSi eta heta0
  refine ⟨Ceta * (3 + (c2Norm (closedCube z r hr) phi) ^ 2), gamma, max Ne1 N0,
    mul_pos hCeta (by positivity), hgamma, ?_⟩
  intro N hN
  have hbad := aux_prop_as_dirichlet_bad model H e he H1 hH1 Dgeom Cgeom eta Ceta gamma N0
    z r hr hFSN (e0 / 8) hx0 hx1 hc2 N (le_of_max_le_right hN)
    (hNe1 N (le_of_max_le_left hN)) hP phi hphi b hb
  have hδ : 0 < Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) :=
    mul_pos hCeta (Real.rpow_pos_of_pos (by norm_num) _)
  have herr : 0 ≤ Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * (c2Norm (closedCube z r hr) phi) ^ 2 :=
    mul_nonneg hδ.le (sq_nonneg _)
  have hA : 2 * (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) +
      Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * (c2Norm (closedCube z r hr) phi) ^ 2 ≤
      Ceta * (3 + (c2Norm (closedCube z r hr) phi) ^ 2) * (3 : ℝ) ^ (-(gamma * (N : ℝ))) := by
    rw [← neg_mul]
    have h3 : Ceta * (3 + (c2Norm (closedCube z r hr) phi) ^ 2) * (3 : ℝ) ^ (-gamma * (N : ℝ)) =
        3 * (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) +
          Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * (c2Norm (closedCube z r hr) phi) ^ 2 := by
      ring
    rw [h3]
    linarith only [hδ]
  have hmain := aux_prop_as_dirichlet_limit_tail (chaosSampleLaw model).toMeasure
    (fun N om => dirichletResponse (killedResponseSpace hP)
        (cutoffPositiveCoefficient model H om N z hr) b) LamE hconv hnn N
    ((1 + e0 / 8) / (1 - e0 / 8) * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom))
    (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * (c2Norm (closedCube z r hr) phi) ^ 2)
    (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) (1 * eps)
    (Ceta * (3 + (c2Norm (closedCube z r hr) phi) ^ 2) * (3 : ℝ) ^ (-(gamma * (N : ℝ))))
    (ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) +
      ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))))
    hq1 hq2 (by linarith only [hqe, he0e]) herr hδ hA hbad
  refine hmain.trans ?_
  rw [← ENNReal.ofReal_add hδ.le hδ.le]
  apply ENNReal.ofReal_le_ofReal
  linarith only [hA, herr]



theorem aux_prop_as_dirichlet_of_limit
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d ⟨by omega⟩)
    (Dbase : @sum_errors_baseline_input d ⟨by omega⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (beta : ℝ) (hbeta_lower : (1 / 2 : ℝ) < beta) (hbeta_upper : beta < 1) :
    ∃ (delta0 Cgeom : ℝ), 0 < delta0 ∧ 0 < Cgeom ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (HI : InfraredCharacterization model H),
        model.delta ≤ min 1 delta0 →
        ∀ (I : Type) [Countable I]
          (z : I → SpatialCoordinates d) (r : I → ℝ)
          (hr : ∀ i, 0 < r i)
          (htriadic : ∀ i, ∃ j : ℤ, r i = (3 : ℝ) ^ j)
          (hP : ∀ i, ∃ K : ℝ≥0,
            ∀ u : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
              ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
                K * ‖subspaceGradient
                  (killedSobolevGraph (centeredCube (z i) (r i) (hr i))) u‖)
          (phi : I → SpatialCoordinates d → ℝ)
          (hphi : ∀ i, ContDiff ℝ ∞ (phi i))
          (b : (i : I) → weakSobolevGraph (centeredCube (z i) (r i) (hr i)))
          (hb : ∀ i,
            ((b i : SobolevData (centeredCube (z i) (r i) (hr i))).1 :
                SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
              (phi i)),
        let Lam : I → ℕ → BilateralField d → ℝ := fun i N omega =>
          dirichletResponse (killedResponseSpace (hP i))
            (cutoffPositiveCoefficient model H omega N (z i) (hr i)) (b i)
        let Bmin : I → ℕ → BilateralField d →
            (SpatialCoordinates d → ℝ) → ℝ := fun i N omega g =>
          sInf {e : ℝ | ∃ (u : weakSobolevGraph (centeredCube (z i) (r i) (hr i)))
              (U : SpatialCoordinates d → ℝ),
            ContinuousOn U (closedCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) ∧
            ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] U ∧
            (∀ x ∈ frontier (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
              U x = g x) ∧
            e = sobolevCoefficientForm
              (cutoffPositiveCoefficient model H omega N (z i) (hr i)) u.val u.val}
        ∀ (RL : I → BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ))
          (hRL : ∀ (i : I) (g : SpatialCoordinates d → ℝ),
            IsCellBoundaryClass beta (z i) (r i) g →
              TendstoInMeasure (chaosSampleLaw model).toMeasure
                (fun N omega => Bmin i N omega g) atTop
                (fun omega => (RL i omega g) ^ 2)),
          (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
            ∀ i : I, ∀ N : ℕ, Lam i N omega = Bmin i N omega (phi i)) ∧
            ∃ LamE : I → BilateralField d → ℝ,
              (∀ i, Measurable (LamE i)) ∧
              (∀ i,
                LamE i =ᵐ[(chaosSampleLaw model).toMeasure]
                  (fun omega => (RL i omega (phi i)) ^ 2)) ∧
              (∀ i,
                TendstoInMeasure (chaosSampleLaw model).toMeasure
                  (Lam i) atTop (LamE i)) ∧
              (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
                ∀ i : I, 0 ≤ LamE i omega) ∧
              (∀ i : I, ∀ eps : ℝ, 0 < eps →
                ∃ (Ce ce : ℝ), ∃ Ne : ℕ,
                  0 < Ce ∧ 0 < ce ∧
                    ∀ N : ℕ, Ne ≤ N →
                      (chaosSampleLaw model).toMeasure
                          {omega |
                            Cgeom * eps * LamE i omega +
                                Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                              |Lam i N omega - LamE i omega|} ≤
                        ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) ∧
              (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
                ∀ i : I, Tendsto (fun N => Lam i N omega) atTop
                  (𝓝 (LamE i omega))) := by
  have hLN0 := lem_local_normalizations d hd Jc Pc Xc Sf W Cp D hES Step Interp (fun z r hr F => inputs_EM_witness d z r hr F) beta hbeta_lower hbeta_upper
  obtain ⟨delta0L, hdelta0L, hLN⟩ := hLN0
  have hFS0 := aux_prop_as_dirichlet_FS_of_lem hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp (1 / 8) (by norm_num)
  obtain ⟨H1, Dgeom, CgeomFS, delta0FS, hH1, _, hCgeomFS, hdelta0FS, hFS⟩ := hFS0
  refine ⟨min delta0L delta0FS, 1, lt_min hdelta0L hdelta0FS, one_pos, ?_⟩
  intro model Rm Sreg It H HI hdelta I _ z r hr htriadic hP phi hphi b hb Lam Bmin RL hRL
  have hdL : model.delta ≤ min 1 delta0L :=
    hdelta.trans (min_le_min le_rfl (min_le_left _ _))
  have hdFS : model.delta ≤ delta0FS :=
    hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLNm := hLN model Rm Sreg It H HI hdL
  obtain ⟨e, RL0, he, hRLconv, -, hpos, -, -, -⟩ := hLNm
  have hwin := aux_prop_as_dirichlet_window hd beta hbeta_upper model H HI.1 e he
    (RL0 0 1 one_pos) (fun g hg => hRLconv 0 1 one_pos g ⟨0, by norm_num⟩ hg)
    (fun p hp => hpos 0 1 one_pos p ⟨0, by norm_num⟩ hp) H1 hH1 Dgeom CgeomFS hCgeomFS
    (hFS model Rm Sreg It H HI hdFS 0 1 one_pos ⟨0, by simp⟩)
  have hbridge : ∀ i N omega, Lam i N omega = Bmin i N omega (phi i) := fun i N omega =>
    aux_prop_as_dirichlet_bridge hd (z i) (r i) (hr i) (hP i) _ (b i) (phi i) (hphi i) (hb i)
  have hmeas : ∀ i N, Measurable (Lam i N) := fun i N =>
    aux_prop_as_dirichlet_response_measurable model H HI.1 N (z i) (r i) (hr i) (hP i) (b i)
  have hconvB : ∀ i, TendstoInMeasure (chaosSampleLaw model).toMeasure (Lam i) atTop
      (fun omega => (RL i omega (phi i)) ^ 2) := by
    intro i
    have hfun : Lam i = fun N omega => Bmin i N omega (phi i) :=
      funext fun N => funext fun omega => hbridge i N omega
    rw [hfun]
    exact hRL i (phi i)
      (aux_prop_as_dirichlet_smooth_class beta hbeta_upper.le (z i) (r i) (phi i) (hphi i))
  choose LamE hLamEm hLamEae using fun i =>
    aux_prop_as_dirichlet_measurable_version (chaosSampleLaw model).toMeasure (Lam i) (hmeas i) _
      (hconvB i)
  have hLamconv : ∀ i, TendstoInMeasure (chaosSampleLaw model).toMeasure (Lam i) atTop (LamE i) :=
    fun i => (hconvB i).congr_right (hLamEae i).symm
  have hnn : ∀ i, ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, 0 ≤ LamE i omega := fun i =>
    (hLamEae i).mono fun omega h => h ▸ sq_nonneg _
  have htail := fun i => aux_prop_as_dirichlet_tail model H e he H1 hH1 Dgeom CgeomFS hCgeomFS
    hwin (z i) (r i) (hr i) (hP i) (phi i) (hphi i) (b i) (hb i)
    (hFS model Rm Sreg It H HI hdFS (z i) (r i) (hr i) (htriadic i)) (LamE i) (hLamconv i) (hnn i)
  refine ⟨ae_of_all _ fun omega i N => hbridge i N omega, LamE, hLamEm, hLamEae, hLamconv,
    ae_all_iff.2 hnn, htail, ?_⟩
  exact ae_all_iff.2 fun i =>
    aux_prop_as_dirichlet_ae_of_tail (chaosSampleLaw model).toMeasure (Lam i) (LamE i) 1 (htail i)

/-- Homogenized Dirichlet response limits under the displayed coefficient, cube and smooth boundary-data hypotheses. The proof combines local normalization, finite-stopping comparisons and tail estimates, then applies Borel--Cantelli to the countable data family. The conclusion includes the measurable random limit and its moment bounds. -/
theorem aux_prop_as_dirichlet_with_representative
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d ⟨by omega⟩)
    (Dbase : @sum_errors_baseline_input d ⟨by omega⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (beta : ℝ) (hbeta_lower : (1 / 2 : ℝ) < beta) (hbeta_upper : beta < 1) :
    ∃ (delta0 Cgeom : ℝ), 0 < delta0 ∧ 0 < Cgeom ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (HI : InfraredCharacterization model H),
        model.delta ≤ min 1 delta0 →
        ∀ (I : Type) [Countable I]
          (z : I → SpatialCoordinates d) (r : I → ℝ)
          (hr : ∀ i, 0 < r i)
          (htriadic : ∀ i, ∃ j : ℤ, r i = (3 : ℝ) ^ j)
          (hP : ∀ i, ∃ K : ℝ≥0,
            ∀ u : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
              ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
                K * ‖subspaceGradient
                  (killedSobolevGraph (centeredCube (z i) (r i) (hr i))) u‖)
          (phi : I → SpatialCoordinates d → ℝ)
          (hphi : ∀ i, ContDiff ℝ ∞ (phi i))
          (b : (i : I) → weakSobolevGraph (centeredCube (z i) (r i) (hr i)))
          (hb : ∀ i,
            ((b i : SobolevData (centeredCube (z i) (r i) (hr i))).1 :
                SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
              (phi i)),
        let Lam : I → ℕ → BilateralField d → ℝ := fun i N omega =>
          dirichletResponse (killedResponseSpace (hP i))
            (cutoffPositiveCoefficient model H omega N (z i) (hr i)) (b i)
        let Bmin : I → ℕ → BilateralField d →
            (SpatialCoordinates d → ℝ) → ℝ := fun i N omega g =>
          sInf {e : ℝ | ∃ (u : weakSobolevGraph (centeredCube (z i) (r i) (hr i)))
              (U : SpatialCoordinates d → ℝ),
            ContinuousOn U (closedCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) ∧
            ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] U ∧
            (∀ x ∈ frontier (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
              U x = g x) ∧
            e = sobolevCoefficientForm
              (cutoffPositiveCoefficient model H omega N (z i) (hr i)) u.val u.val}
        ∃ RL : I → BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ),
          (∀ (i : I) (g : SpatialCoordinates d → ℝ),
            IsCellBoundaryClass beta (z i) (r i) g →
              TendstoInMeasure (chaosSampleLaw model).toMeasure
                (fun N omega => Bmin i N omega g) atTop
                (fun omega => (RL i omega g) ^ 2)) ∧
          (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
            ∀ i : I, ∀ N : ℕ, Lam i N omega = Bmin i N omega (phi i)) ∧
            ∃ LamE : I → BilateralField d → ℝ,
              (∀ i, Measurable (LamE i)) ∧
              (∀ i,
                LamE i =ᵐ[(chaosSampleLaw model).toMeasure]
                  (fun omega => (RL i omega (phi i)) ^ 2)) ∧
              (∀ i,
                TendstoInMeasure (chaosSampleLaw model).toMeasure
                  (Lam i) atTop (LamE i)) ∧
              (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
                ∀ i : I, 0 ≤ LamE i omega) ∧
              (∀ i : I, ∀ eps : ℝ, 0 < eps →
                ∃ (Ce ce : ℝ), ∃ Ne : ℕ,
                  0 < Ce ∧ 0 < ce ∧
                    ∀ N : ℕ, Ne ≤ N →
                      (chaosSampleLaw model).toMeasure
                          {omega |
                            Cgeom * eps * LamE i omega +
                                Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                              |Lam i N omega - LamE i omega|} ≤
                        ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) ∧
              (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
                ∀ i : I, Tendsto (fun N => Lam i N omega) atTop
                  (𝓝 (LamE i omega))) := by
  have hLN0 := lem_local_normalizations d hd Jc Pc Xc Sf W Cp D hES Step Interp (fun z r hr F => inputs_EM_witness d z r hr F) beta hbeta_lower hbeta_upper
  rcases hLN0 with ⟨delta0L, hdelta0L, hLN⟩
  have hC0 :=
    aux_prop_as_dirichlet_of_limit d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp beta hbeta_lower hbeta_upper
  rcases hC0 with ⟨delta0C, Cgeom, hdelta0C, hCgeom, hC⟩
  refine ⟨min delta0L delta0C, Cgeom, lt_min hdelta0L hdelta0C, hCgeom, ?_⟩
  intro model Rm Sreg It H HI hdelta I _ z r hr htriadic hP phi hphi b hb Lam Bmin
  have hdL : model.delta ≤ min 1 delta0L :=
    hdelta.trans (min_le_min le_rfl (min_le_left _ _))
  have hdC : model.delta ≤ min 1 delta0C :=
    hdelta.trans (min_le_min le_rfl (min_le_right _ _))
  have hLNm := hLN model Rm Sreg It H HI hdL
  rcases hLNm with ⟨e, RL0, -, hRLconv, -, -, -, -, -⟩
  -- the actual local-normalization limit, restricted to the family's cubes
  have hRL : ∀ (i : I) (g : SpatialCoordinates d → ℝ),
      IsCellBoundaryClass beta (z i) (r i) g →
        TendstoInMeasure (chaosSampleLaw model).toMeasure
          (fun N omega => Bmin i N omega g) atTop
          (fun omega => (RL0 (z i) (r i) (hr i) omega g) ^ 2) :=
    fun i g hg => hRLconv (z i) (r i) (hr i) g (htriadic i) hg
  exact ⟨fun i => RL0 (z i) (r i) (hr i), hRL,
    hC model Rm Sreg It H HI hdC I z r hr htriadic hP phi hphi b hb
      (fun i => RL0 (z i) (r i) (hr i)) hRL⟩

theorem aux_prop_as_dirichlet_cube_poincare_witness
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) :
    ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖ := by
  have : NeZero d := ⟨by omega⟩
  let Q := centeredCube z r hr
  have hQ : Homogenization.IsOpenBoundedConvexDomain
      (Q : Set (SpatialCoordinates d)) := by
    refine ⟨Q.isOpen, ?_, ?_⟩
    · simpa [Q] using
        (Homogenization.Bornology.IsBounded.isBoundedDomain
          (centeredCube_isBounded z hr))
    · simpa [Q, centeredCube] using (convex_ball z (r / 2))
  exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain Q hQ).1

theorem aux_prop_as_dirichlet_smooth_weak_witness
    {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (phi : SpatialCoordinates d → ℝ)
    (hphi : ContDiff ℝ ∞ phi) :
    ∃ b : weakSobolevGraph (centeredCube z r hr),
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))] phi := by
  let Q := centeredCube z r hr
  have hgeom : Homogenization.IsOpenBoundedConvexDomain
      (Q : Set (SpatialCoordinates d)) :=
    lane2_isOpenBoundedConvexDomain_centeredCube z hr
  let phiH : H1Function (Q : Set (SpatialCoordinates d)) :=
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain hgeom
      (hphi.of_le (by simp))
  refine ⟨⟨sobolevDataOfH1 phiH, sobolevDataOfH1_mem_weak phiH⟩, ?_⟩
  simpa only [phiH, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain] using
    (sobolevDataOfH1_fst_coeFn phiH)

/-- Source-facing Dirichlet response theorem: the cube Poincaré witness and
smooth datum's Sobolev representative are constructed, not assumed. -/
theorem prop_as_dirichlet
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d ⟨by omega⟩)
    (Dbase : @sum_errors_baseline_input d ⟨by omega⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (beta : ℝ) (hbeta_lower : (1 / 2 : ℝ) < beta) (hbeta_upper : beta < 1) :
    ∃ (delta0 Cgeom : ℝ), 0 < delta0 ∧ 0 < Cgeom ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (HI : InfraredCharacterization model H),
        model.delta ≤ min 1 delta0 →
        ∀ (I : Type) [Countable I]
          (z : I → SpatialCoordinates d) (r : I → ℝ)
          (hr : ∀ i, 0 < r i)
          (htriadic : ∀ i, ∃ j : ℤ, r i = (3 : ℝ) ^ j)
          (phi : I → SpatialCoordinates d → ℝ)
          (hphi : ∀ i, ContDiff ℝ ∞ (phi i)),
        let hP : ∀ i, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
            ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
              K * ‖subspaceGradient
                (killedSobolevGraph (centeredCube (z i) (r i) (hr i))) u‖ :=
          fun i => aux_prop_as_dirichlet_cube_poincare_witness hd (z i) (r i) (hr i)
        let b : (i : I) → weakSobolevGraph (centeredCube (z i) (r i) (hr i)) :=
          fun i => Classical.choose
            (aux_prop_as_dirichlet_smooth_weak_witness (z i) (r i) (hr i) (phi i) (hphi i))
        let Lam : I → ℕ → BilateralField d → ℝ := fun i N omega =>
          dirichletResponse (killedResponseSpace (hP i))
            (cutoffPositiveCoefficient model H omega N (z i) (hr i)) (b i)
        let Bmin : I → ℕ → BilateralField d →
            (SpatialCoordinates d → ℝ) → ℝ := fun i N omega g =>
          sInf {e : ℝ | ∃ (u : weakSobolevGraph (centeredCube (z i) (r i) (hr i)))
              (U : SpatialCoordinates d → ℝ),
            ContinuousOn U (closedCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) ∧
            ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] U ∧
            (∀ x ∈ frontier (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
              U x = g x) ∧
            e = sobolevCoefficientForm
              (cutoffPositiveCoefficient model H omega N (z i) (hr i)) u.val u.val}
        ∃ RL : I → BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ),
          (∀ (i : I) (g : SpatialCoordinates d → ℝ),
            IsCellBoundaryClass beta (z i) (r i) g →
              TendstoInMeasure (chaosSampleLaw model).toMeasure
                (fun N omega => Bmin i N omega g) atTop
                (fun omega => (RL i omega g) ^ 2)) ∧
          (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
            ∀ i : I, ∀ N : ℕ, Lam i N omega = Bmin i N omega (phi i)) ∧
            ∃ LamE : I → BilateralField d → ℝ,
              (∀ i, Measurable (LamE i)) ∧
              (∀ i,
                LamE i =ᵐ[(chaosSampleLaw model).toMeasure]
                  (fun omega => (RL i omega (phi i)) ^ 2)) ∧
              (∀ i,
                TendstoInMeasure (chaosSampleLaw model).toMeasure
                  (Lam i) atTop (LamE i)) ∧
              (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
                ∀ i : I, 0 ≤ LamE i omega) ∧
              (∀ i : I, ∀ eps : ℝ, 0 < eps →
                ∃ (Ce ce : ℝ), ∃ Ne : ℕ,
                  0 < Ce ∧ 0 < ce ∧
                    ∀ N : ℕ, Ne ≤ N →
                      (chaosSampleLaw model).toMeasure
                          {omega |
                            Cgeom * eps * LamE i omega +
                                Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                              |Lam i N omega - LamE i omega|} ≤
                        ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) ∧
              (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
                ∀ i : I, Tendsto (fun N => Lam i N omega) atTop
                  (𝓝 (LamE i omega))) := by
  obtain ⟨delta0, Cgeom, hdelta0, hCgeom, hmain⟩ :=
    aux_prop_as_dirichlet_with_representative d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
      beta hbeta_lower hbeta_upper
  refine ⟨delta0, Cgeom, hdelta0, hCgeom, ?_⟩
  intro model Rm Sreg It H HI hdelta I _ z r hr htriadic phi hphi
  let hP : ∀ i, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
      ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph (centeredCube (z i) (r i) (hr i))) u‖ :=
    fun i => aux_prop_as_dirichlet_cube_poincare_witness hd (z i) (r i) (hr i)
  let b : (i : I) → weakSobolevGraph (centeredCube (z i) (r i) (hr i)) :=
    fun i => Classical.choose
      (aux_prop_as_dirichlet_smooth_weak_witness (z i) (r i) (hr i) (phi i) (hphi i))
  have hb : ∀ i,
      ((b i : SobolevData (centeredCube (z i) (r i) (hr i))).1 :
          SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))]
        (phi i) :=
    fun i => Classical.choose_spec
      (aux_prop_as_dirichlet_smooth_weak_witness (z i) (r i) (hr i) (phi i) (hphi i))
  exact hmain model Rm Sreg It H HI hdelta I z r hr htriadic hP phi hphi b hb

end SubdiffusiveProcess.Paper
