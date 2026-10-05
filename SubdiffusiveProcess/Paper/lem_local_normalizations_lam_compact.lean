module

public import SubdiffusiveProcess.Paper.lnorm_smooth_dirichlet_response_compact
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.Sobolev.AffineData
public import SubdiffusiveProcess.Lnorm.LpClusters
public import Homogenization.Sobolev.H1.BasicLemmas

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.ResponseMoments
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff Pointwise Distributions

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section LamCompactHelpers

variable {d : ℕ}

def aux_lem_local_normalizations_lam_compact_Lset {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) : Set ℝ :=
  {e : ℝ | ∃ (u : weakSobolevGraph (centeredCube z r hr))
      (U : SpatialCoordinates d → ℝ),
    ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
    ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
    (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = g x) ∧
    e = sobolevCoefficientForm a u.val u.val}

theorem aux_lem_local_normalizations_lam_compact_Lset_nonneg (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) :
    ∀ e ∈ aux_lem_local_normalizations_lam_compact_Lset z r hr a g, 0 ≤ e := by
  rintro e ⟨u, U, -, -, -, rfl⟩
  exact sobolevCoefficientForm_nonneg a u.val

theorem aux_lem_local_normalizations_lam_compact_sInf_nonneg (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) :
    0 ≤ sInf (aux_lem_local_normalizations_lam_compact_Lset z r hr a g) :=
  Real.sInf_nonneg (aux_lem_local_normalizations_lam_compact_Lset_nonneg z r hr a g)

theorem aux_lem_local_normalizations_lam_compact_Lset_bdd (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) :
    BddBelow (aux_lem_local_normalizations_lam_compact_Lset z r hr a g) :=
  ⟨0, aux_lem_local_normalizations_lam_compact_Lset_nonneg z r hr a g⟩

theorem aux_lem_local_normalizations_lam_compact_cont_competitor
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr))
    (g G : SpatialCoordinates d → ℝ)
    (hGc : ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G)
    (hGg : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), G x = g x)
    (ψ : 𝓓(centeredCube z r hr, ℝ)) :
    sobolevCoefficientForm a (b.val + smoothSobolevData ψ) (b.val + smoothSobolevData ψ) ∈
      aux_lem_local_normalizations_lam_compact_Lset z r hr a g := by
  let u : weakSobolevGraph (centeredCube z r hr) :=
    ⟨b.val + smoothSobolevData ψ,
      (weakSobolevGraph (centeredCube z r hr)).add_mem b.property (smoothSobolevData_mem ψ)⟩
  refine ⟨u, fun x => G x + ψ x, ?_, ?_, ?_, rfl⟩
  · exact hGc.add ψ.contDiff.continuous.continuousOn
  · filter_upwards [Lp.coeFn_add b.val.1 (testL2 ψ), hb, testL2_coeFn ψ] with x hadd hbx hψx
    change ((b.val.1 + testL2 ψ : DomainL2 (centeredCube z r hr)) :
      SpatialCoordinates d → ℝ) x = G x + ψ x
    rw [hadd, Pi.add_apply, hbx, hψx]
  · intro x hx
    have hxnot : x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      have hopen : IsOpen (centeredCube z r hr : Set (SpatialCoordinates d)) :=
        (centeredCube z r hr).isOpen
      rw [hopen.frontier_eq] at hx
      exact hx.2
    have hψ0 : ψ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hxnot (ψ.tsupport_subset h))
    simp only [hψ0, add_zero, hGg x hx]

theorem aux_lem_local_normalizations_lam_compact_sInf_le_response
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0,
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient
            (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr))
    (g G : SpatialCoordinates d → ℝ)
    (hGc : ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G)
    (hGg : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), G x = g x) :
    sInf (aux_lem_local_normalizations_lam_compact_Lset z r hr a g) ≤
      dirichletResponse (killedResponseSpace hP) a b := by
  have hmem : (dirichletMinimizer (killedResponseSpace hP) a b).val - b.val ∈
      killedSobolevGraph (centeredCube z r hr) :=
    dirichletMinimizer_mem_affine (killedResponseSpace hP) a b
  have hcl : (dirichletMinimizer (killedResponseSpace hP) a b).val - b.val ∈ closure
      ((LinearMap.range (smoothSobolevDataLinear (Ω := centeredCube z r hr)) :
        Submodule ℝ (SobolevData (centeredCube z r hr))) :
          Set (SobolevData (centeredCube z r hr))) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hmem
  obtain ⟨x, hxmem, hxlim⟩ := mem_closure_iff_seq_limit.mp hcl
  choose ψ hψ using hxmem
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
  have hlim : Tendsto (fun n => sobolevCoefficientForm a (b.val + smoothSobolevData (ψ n))
      (b.val + smoothSobolevData (ψ n))) atTop
      (𝓝 (dirichletResponse (killedResponseSpace hP) a b)) := (hform.tendsto _).comp hconv
  refine ge_of_tendsto' hlim (fun n => ?_)
  exact csInf_le (aux_lem_local_normalizations_lam_compact_Lset_bdd z r hr a g)
    (aux_lem_local_normalizations_lam_compact_cont_competitor z r hr a b g G hGc hb hGg (ψ n))

theorem aux_lem_local_normalizations_lam_compact_response_le_sInf
    (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0,
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient
            (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr))
    (g G : SpatialCoordinates d → ℝ)
    (hGc : ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G)
    (hGg : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), G x = g x) :
    dirichletResponse (killedResponseSpace hP) a b ≤
      sInf (aux_lem_local_normalizations_lam_compact_Lset z r hr a g) := by
  have hne : (aux_lem_local_normalizations_lam_compact_Lset z r hr a g).Nonempty := by
    exact ⟨sobolevCoefficientForm a b.val b.val, ⟨b, G, hGc, hb, hGg, rfl⟩⟩
  apply le_csInf hne
  rintro e ⟨u, U, hUc, huU, hUb, rfl⟩
  let v : weakSobolevGraph (centeredCube z r hr) :=
    ⟨u.val - b.val, (weakSobolevGraph (centeredCube z r hr)).sub_mem u.property b.property⟩
  have hvrep : ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] (U - G) := by
    filter_upwards [Lp.coeFn_sub u.val.1 b.val.1, huU, hb] with x hsub hxu hbx
    change ((u.val.1 - b.val.1 : DomainL2 (centeredCube z r hr)) :
      SpatialCoordinates d → ℝ) x = U x - G x
    rw [hsub, Pi.sub_apply, hxu, hbx]
  have hvzero : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      (U - G) x = 0 := by
    intro x hx
    simp only [Pi.sub_apply, hUb x hx, hGg x hx, sub_self]
  have hvk : (v : SobolevData (centeredCube z r hr)) ∈
      killedSobolevGraph (centeredCube z r hr) :=
    lem_extension_trace_class_transport hd z r hr v (U - G) (hUc.sub hGc) hvrep hvzero
  let w : (killedResponseSpace hP).space := ⟨v.val, hvk⟩
  have hsum : b.val + w.val = u.val := by
    change b.val + (u.val - b.val) = u.val
    abel
  have hleast := dirichletResponse_isLeast (killedResponseSpace hP) a b
  have hle := hleast.2 ⟨w, rfl⟩
  change dirichletResponse (killedResponseSpace hP) a b ≤
    sobolevCoefficientForm a (b.val + w.val) (b.val + w.val) at hle
  rw [hsum] at hle
  exact hle

def aux_lem_local_normalizations_lam_compact_Lam
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (N : ℕ) (omega : BilateralField d)
    (g : SpatialCoordinates d → ℝ) : ℝ :=
  sInf (aux_lem_local_normalizations_lam_compact_Lset z r hr (cutoffPositiveCoefficient M H omega N z hr) g)

theorem aux_lem_local_normalizations_lam_compact_Lam_eq_response
    (hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0,
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient
            (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr))
    (g G : SpatialCoordinates d → ℝ)
    (hGc : ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G)
    (hGg : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), G x = g x)
    (ha : a = cutoffPositiveCoefficient M H omega N z hr) :
    aux_lem_local_normalizations_lam_compact_Lam M H z r hr N omega g =
      dirichletResponse (killedResponseSpace hP) a b := by
  unfold aux_lem_local_normalizations_lam_compact_Lam
  exact le_antisymm
    (by simpa [ha] using
      (aux_lem_local_normalizations_lam_compact_sInf_le_response z r hr hP a b g G hGc hb hGg))
    (by simpa [ha] using
      (aux_lem_local_normalizations_lam_compact_response_le_sInf hd z r hr hP a b g G hGc hb hGg))

theorem aux_lem_local_normalizations_lam_compact_form_const (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (v : SobolevData (centeredCube z r hr)) (c : ℝ) :
    sobolevCoefficientForm a v (affineSobolevData (centeredCube_isBounded z hr) 0 c) = 0 := by
  rw [sobolevCoefficientForm_apply]
  apply Finset.sum_eq_zero
  intro i _
  have h : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      a.val x * (v.2 i x * (affineSobolevData (centeredCube_isBounded z hr) 0 c).2 i x) = 0 := by
    filter_upwards [domainConstantL2_coeFn (Ω := centeredCube z r hr) ((0 : Fin d → ℝ) i)]
      with x hx
    change a.val x * (v.2 i x * (domainConstantL2 (Ω := centeredCube z r hr)
      ((0 : Fin d → ℝ) i)) x) = 0
    rw [hx]; simp
  rw [integral_congr_ae h, integral_zero]

theorem aux_lem_local_normalizations_lam_compact_lnorm_isOpenBoundedConvexDomain {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    Homogenization.IsOpenBoundedConvexDomain (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  have hcube : (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) := rfl
  rw [hcube]
  refine ⟨Metric.isOpen_ball, ⟨‖z‖ + r / 2, by positivity, ?_⟩, convex_ball z (r / 2)⟩
  intro x hx i
  have hxz : dist x z < r / 2 := hx
  have hi : dist (x i) (z i) ≤ dist x z := dist_le_pi_dist x z i
  have hzi : |z i| ≤ ‖z‖ := by
    simpa [Real.norm_eq_abs] using (norm_le_pi_norm z i)
  have hxzi : |x i - z i| ≤ r / 2 := by
    have := hi.trans hxz.le
    simpa [Real.dist_eq] using this
  have htri : |x i| ≤ |x i - z i| + |z i| := by
    have heq : x i = (x i - z i) + z i := by ring
    calc |x i| = |(x i - z i) + z i| := by rw [← heq]
      _ ≤ |x i - z i| + |z i| := by
          simpa [Real.norm_eq_abs] using norm_add_le (x i - z i) (z i)
  calc |x i| ≤ |x i - z i| + |z i| := htri
    _ ≤ r / 2 + ‖z‖ := add_le_add hxzi hzi
    _ = ‖z‖ + r / 2 := by ring

theorem aux_lem_local_normalizations_lam_compact_lnorm_hP_general (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖ := by
  have : NeZero d := ⟨by omega⟩
  exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
    (centeredCube z r hr) (aux_lem_local_normalizations_lam_compact_lnorm_isOpenBoundedConvexDomain z r hr)).1

theorem aux_lem_local_normalizations_lam_compact_lnorm_affine_nonconst (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
        (∑ i : Fin d, (1 : ℝ) * x i) ≠ ∑ i : Fin d, (1 : ℝ) * y i := by
  have hcube : (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) := rfl
  have hfr : frontier (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Metric.sphere z (r / 2) := by
    rw [hcube]; exact frontier_ball z (half_pos hr).ne'
  have hi0 : (0 : ℕ) < d := by omega
  set i0 : Fin d := ⟨0, hi0⟩ with hi0def
  set p : SpatialCoordinates d := fun i => z i + (if i = i0 then r / 2 else 0) with hpdef
  set q : SpatialCoordinates d := fun i => z i - (if i = i0 then r / 2 else 0) with hqdef
  have hmemsphere : ∀ s : SpatialCoordinates d, (∀ i, dist (s i) (z i) ≤ r / 2) →
      dist (s i0) (z i0) = r / 2 → s ∈ Metric.sphere z (r / 2) := by
    intro s hall heq
    rw [sphere_pi z (Or.inl (half_pos hr))]
    exact ⟨Set.mem_iUnion.mpr ⟨i0, heq⟩, (Metric.mem_closedBall).mpr
      ((dist_pi_le_iff (half_pos hr).le).mpr hall)⟩
  have hdist_pos : dist (p i0) (z i0) = r / 2 := by
    have heq : p i0 - z i0 = r / 2 := by
      show z i0 + (if i0 = i0 then r / 2 else 0) - z i0 = r / 2
      rw [ite_eq_left rfl]; ring
    rw [Real.dist_eq, heq, abs_of_nonneg (half_pos hr).le]
  have hdist_neg : dist (q i0) (z i0) = r / 2 := by
    have heq : q i0 - z i0 = -(r / 2) := by
      show z i0 - (if i0 = i0 then r / 2 else 0) - z i0 = -(r / 2)
      rw [ite_eq_left rfl]; ring
    rw [Real.dist_eq, heq, abs_neg, abs_of_nonneg (half_pos hr).le]
  have hbound_p : ∀ i, dist (p i) (z i) ≤ r / 2 := by
    intro i
    by_cases hi : i = i0
    · subst hi; rw [hdist_pos]
    · have heq : p i - z i = 0 := by
        show z i + (if i = i0 then r / 2 else 0) - z i = 0
        rw [ite_eq_right hi]; ring
      rw [Real.dist_eq, heq, abs_zero]; exact (half_pos hr).le
  have hbound_q : ∀ i, dist (q i) (z i) ≤ r / 2 := by
    intro i
    by_cases hi : i = i0
    · subst hi; rw [hdist_neg]
    · have heq : q i - z i = 0 := by
        show z i - (if i = i0 then r / 2 else 0) - z i = 0
        rw [ite_eq_right hi]; ring
      rw [Real.dist_eq, heq, abs_zero]; exact (half_pos hr).le
  refine ⟨p, ?_, q, ?_, ?_⟩
  · rw [hfr]; exact hmemsphere p hbound_p hdist_pos
  · rw [hfr]; exact hmemsphere q hbound_q hdist_neg
  · have hsum : (∑ i : Fin d, (1 : ℝ) * p i) - ∑ i : Fin d, (1 : ℝ) * q i =
        ∑ i : Fin d, (1 : ℝ) * (p i - q i) := by
      rw [← Finset.sum_sub_distrib]; congr 1; funext i; ring
    have hpq : ∀ i : Fin d, p i - q i = if i = i0 then r else 0 := by
      intro i
      by_cases hi : i = i0
      · subst hi
        show z i0 + (if i0 = i0 then r / 2 else 0) -
          (z i0 - (if i0 = i0 then r / 2 else 0)) = r
        rw [ite_eq_left rfl]; ring
      · show z i + (if i = i0 then r / 2 else 0) -
          (z i - (if i = i0 then r / 2 else 0)) = if i = i0 then r else 0
        rw [ite_eq_right hi, ite_eq_right hi]; ring
    have hval : (∑ i : Fin d, (1 : ℝ) * p i) - ∑ i : Fin d, (1 : ℝ) * q i = r := by
      rw [hsum]
      simp only [hpq, mul_ite, mul_zero, one_mul]
      rw [Finset.sum_ite_eq' Finset.univ i0 (fun _ : Fin d => r)]
      simp
    intro hcontra
    rw [hcontra, sub_self] at hval
    exact hr.ne' hval.symm

theorem aux_lem_local_normalizations_lam_compact_smooth_representative
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (g : SpatialCoordinates d → ℝ) (hg : ContDiff ℝ ∞ g) :
    ∃ b : weakSobolevGraph (centeredCube z r hr),
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g := by
  let v := Homogenization.H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (aux_lem_local_normalizations_lam_compact_lnorm_isOpenBoundedConvexDomain z r hr) (hg.of_le (by norm_num))
  obtain ⟨b, hb, -⟩ := exists_weakSobolevGraph_of_nativeH1 v
  exact ⟨b, hb⟩

theorem aux_lem_local_normalizations_lam_compact_Lam_eq_zero_of_constant_trace
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (N : ℕ) (omega : BilateralField d) (g : SpatialCoordinates d → ℝ) (c : ℝ)
    (hg : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), g x = c) :
    aux_lem_local_normalizations_lam_compact_Lam M H z r hr N omega g = 0 := by
  let a := cutoffPositiveCoefficient M H omega N z hr
  have hz : 0 ∈ aux_lem_local_normalizations_lam_compact_Lset z r hr a g := by
    refine ⟨affineSobolev (centeredCube_isBounded z hr) 0 c, fun _ => c,
      continuousOn_const, ?_, fun x hx => (hg x hx).symm, ?_⟩
    · filter_upwards [affineL2_coeFn (centeredCube_isBounded z hr) (0 : Fin d → ℝ) c]
        with x hx
      change (affineL2 (centeredCube_isBounded z hr) (0 : Fin d → ℝ) c) x = c
      simpa only [affineSlope_apply, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
        zero_add] using hx
    · exact (aux_lem_local_normalizations_lam_compact_form_const z r hr a
        (affineSobolevData (centeredCube_isBounded z hr) 0 c) c).symm
  exact le_antisymm
    (csInf_le ⟨0, aux_lem_local_normalizations_lam_compact_Lset_nonneg z r hr a g⟩ hz)
    (aux_lem_local_normalizations_lam_compact_sInf_nonneg z r hr a g)

end LamCompactHelpers

/-- Every cutoff subsequence of the actual variational responses `Λ_N` on a cube of side at most one,
for a smooth datum, has an almost surely convergent further subsequence: strong relative
compactness of the finite-cutoff responses, at one disorder threshold chosen before the model, the
cube and the datum.  No uniqueness of the limit is asserted. -/
theorem lem_local_normalizations_lam_compact
    (d : ℕ) (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
        ∀ g : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ g →
        ∀ ψ : ℕ → ℕ, StrictMono ψ →
          ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧ ∃ L : BilateralField d → ℝ,
            ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              Tendsto (fun n => aux_lem_local_normalizations_lam_compact_Lam M H z r hr
                (ψ (ψ' n)) omega g) atTop (𝓝 (L omega)) := by
  classical
  have instLpTwo : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2) := ⟨by norm_num⟩
  obtain ⟨δ, hδ, hsm⟩ := lnorm_smooth_dirichlet_response_compact d hd Jc Pc Xc W Sf D
  refine ⟨δ, hδ, ?_⟩
  intro M Rm Sreg It H HI hM z r hr hrle g hg ψ hψ
  by_cases hn : ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), g x ≠ g y
  · obtain ⟨b, hb⟩ := aux_lem_local_normalizations_lam_compact_smooth_representative z r hr g hg
    have hP := aux_lem_local_normalizations_lam_compact_lnorm_hP_general d hd z r hr
    obtain ⟨hmem, hcompact⟩ := hsm M Rm Sreg It H HI hM z r hr hrle hP g hg hn b hb
    obtain ⟨ψ', hψ', L, -, hL⟩ := SubdiffusiveProcess.Lnorm.ae_subseq_of_lp_compact (chaosSampleLaw M).toMeasure
      (ENNReal.ofReal 2) ENNReal.ofReal_ne_top _ hmem hcompact ψ
    refine ⟨ψ', hψ', L, ?_⟩
    filter_upwards [hL] with omega homega
    have heq : ∀ n, aux_lem_local_normalizations_lam_compact_Lam M H z r hr
        (ψ (ψ' n)) omega g = dirichletResponse (killedResponseSpace hP)
          (cutoffPositiveCoefficient M H omega (ψ (ψ' n)) z hr) b := fun n =>
      aux_lem_local_normalizations_lam_compact_Lam_eq_response hd M H omega (ψ (ψ' n))
        z hr hP (cutoffPositiveCoefficient M H omega (ψ (ψ' n)) z hr)
        b g g hg.continuous.continuousOn hb (fun _ _ => rfl) rfl
    exact homega.congr' (Eventually.of_forall fun n => (heq n).symm)
  · push Not at hn
    by_cases hfr : (frontier (centeredCube z r hr : Set (SpatialCoordinates d))).Nonempty
    · obtain ⟨x0, hx0⟩ := hfr
      refine ⟨id, strictMono_id, fun _ => 0, Eventually.of_forall fun omega => ?_⟩
      have heq : ∀ n, aux_lem_local_normalizations_lam_compact_Lam M H z r hr
          (ψ (id n)) omega g = 0 := fun n =>
        aux_lem_local_normalizations_lam_compact_Lam_eq_zero_of_constant_trace M H z r hr
          (ψ (id n)) omega g (g x0) (fun w hw => hn w hw x0 hx0)
      exact tendsto_const_nhds.congr' (Eventually.of_forall fun n => (heq n).symm)
    · exfalso
      exact hfr (by
        obtain ⟨x, hx, -, -⟩ := aux_lem_local_normalizations_lam_compact_lnorm_affine_nonconst d hd z r hr
        exact ⟨x, hx⟩)


end SubdiffusiveProcess.Paper
