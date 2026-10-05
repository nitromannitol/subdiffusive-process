module

public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.in_represented_bounds
public import SubdiffusiveProcess.Paper.prop_killed_inverse_dirichlet_form
public import SubdiffusiveProcess.Paper.prop_regularity

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ContDiff
namespace SubdiffusiveProcess.Paper

theorem aux_lem_endpoints_support_1_endpoint_invariance_bounds_side_fields
    {d : ℕ} (hd : 2 ≤ d)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0))
    (G : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N : ℕ → ℕ)
    (hbundle : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 S G N) :
    ∃ (D : Submodule ℚ (DomainL2 (centeredCube z0 r0 hr0)))
      (phi : D → Homogenization.H1Function (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)))
      (alpha : ℝ),
      Dense (D : Set (DomainL2 (centeredCube z0 r0 hr0))) ∧
      (∀ f : D, ContDiff ℝ (⊤ : ℕ∞) (phi f).toFun ∧
        HasCompactSupport (phi f).toFun ∧
        tsupport (phi f).toFun ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ∧
        (sobolevDataOfH1 (phi f)).1 = f.val) ∧
      (∀ f : D, ∃ Cphi : ℝ, 0 ≤ Cphi ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        ∃ vN : ℕ → S.space, ∃ vcN : ℕ → SpatialCoordinates d → ℝ,
        ∃ Kset : Set (SpatialCoordinates d),
          IsCompact Kset ∧ Kset ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ∧
          ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
            (vN n).val.1
              =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] vcN n ∧
            ContinuousOn (vcN n) (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) ∧
            (∀ x ∈ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) \ Kset, vcN n x = 0) ∧
            _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
              (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (vcN n) ∧
            _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
              (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (vcN n) ≤ M ∧
            responseForm S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z0 hr0)
              (vN n) (vN n) ≤ M ∧
            ∀ x ∈ closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)),
              |vcN n x - (phi f).toFun x| ≤ Cphi * (r0 / (3 : ℝ) ^ k)) ∧
      (∀ f : SpatialCoordinates d → ℝ, Continuous f → HasCompactSupport f →
        tsupport f ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) →
        ∀ ε : ℝ, 0 < ε →
        ∃ g : D, ∀ x : SpatialCoordinates d, |(phi g).toFun x - f x| ≤ ε) := by
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨D, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨hDdense, hbundle⟩ := hbundle
  obtain ⟨phi, hbundle⟩ := hbundle
  obtain ⟨hPhi, hbundle⟩ := hbundle
  obtain ⟨alpha, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨_, hbundle⟩ := hbundle
  obtain ⟨hFiniteMesh, hbundle⟩ := hbundle
  obtain ⟨hsmooth, _⟩ := hbundle
  exact ⟨D, phi, alpha, hDdense, hPhi, hFiniteMesh, hsmooth⟩

theorem aux_lem_endpoints_support_1_endpoint_invariance_hFM_fields
    {d : ℕ} (_hd : 2 ≤ d)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0)) (N : ℕ → ℕ)
    (D : Submodule ℚ (DomainL2 (centeredCube z0 r0 hr0)))
    (phi : D → Homogenization.H1Function (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)))
    (alpha : ℝ) (g : D) (Cphi : ℝ) (k0 : ℕ) (k : ℕ) (hk0k : k0 ≤ k)
    (hFM : ∀ k : ℕ, k0 ≤ k →
      ∃ vN : ℕ → S.space, ∃ vcN : ℕ → SpatialCoordinates d → ℝ,
      ∃ Kset : Set (SpatialCoordinates d),
        IsCompact Kset ∧ Kset ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
          (vN n).val.1
            =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] vcN n ∧
          ContinuousOn (vcN n) (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) \ Kset, vcN n x = 0) ∧
          _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
            (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (vcN n) ∧
          _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
            (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (vcN n) ≤ M ∧
          responseForm S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z0 hr0)
            (vN n) (vN n) ≤ M ∧
          ∀ x ∈ closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)),
            |vcN n x - (phi g).toFun x| ≤ Cphi * (r0 / (3 : ℝ) ^ k)) :
    ∃ (vN : ℕ → S.space) (vcN : ℕ → SpatialCoordinates d → ℝ) (M : ℝ),
      (∀ n : ℕ, (vN n).val.1
        =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] vcN n) ∧
      (∀ n : ℕ, responseForm S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z0 hr0)
        (vN n) (vN n) ≤ M) ∧
      (∀ n : ℕ, ∀ x ∈ closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)),
        |vcN n x - (phi g).toFun x| ≤ Cphi * (r0 / (3 : ℝ) ^ k)) := by
  obtain ⟨vN, vcN, Kset, -, -, M, hM0, hconj⟩ := hFM k hk0k
  exact ⟨vN, vcN, M, fun n => (hconj n).1, fun n => (hconj n).2.2.2.2.2.1,
    fun n => (hconj n).2.2.2.2.2.2⟩

theorem aux_lem_endpoints_support_1_endpoint_invariance_hk_of_Cphi
    (Cphi : ℝ) (hCphi0 : 0 ≤ Cphi) (k0 : ℕ) (r0 : ℝ) (hr0 : 0 < r0)
    (ε' : ℝ) (hε'pos : 0 < ε') :
    ∃ k : ℕ, k0 ≤ k ∧ Cphi * (r0 / (3 : ℝ) ^ k) ≤ ε' := by
  by_cases hCphi0eq : Cphi = 0
  · exact ⟨k0, le_refl k0, by rw [hCphi0eq]; simp; positivity⟩
  · have hCphi0pos : 0 < Cphi := lt_of_le_of_ne hCphi0 (Ne.symm hCphi0eq)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (div_pos hε'pos (mul_pos hCphi0pos hr0)) (show (1 / 3 : ℝ) < 1 by norm_num)
    refine ⟨max n k0, le_max_right n k0, ?_⟩
    have hpow : (1 / 3 : ℝ) ^ (max n k0) ≤ (1 / 3 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left n k0)
    have hstep : (1 / 3 : ℝ) ^ (max n k0) * (Cphi * r0) < ε' := by
      calc (1 / 3 : ℝ) ^ (max n k0) * (Cphi * r0)
          ≤ (1 / 3 : ℝ) ^ n * (Cphi * r0) :=
            mul_le_mul_of_nonneg_right hpow (mul_pos hCphi0pos hr0).le
        _ < (ε' / (Cphi * r0)) * (Cphi * r0) :=
            mul_lt_mul_of_pos_right hn (mul_pos hCphi0pos hr0)
        _ = ε' := div_mul_cancel₀ ε' (mul_pos hCphi0pos hr0).ne'
    have hrw : Cphi * (r0 / (3 : ℝ) ^ (max n k0)) =
        (1 / 3 : ℝ) ^ (max n k0) * (Cphi * r0) := by
      rw [div_pow, one_pow]; ring
    rw [hrw]; exact hstep.le

theorem aux_lem_endpoints_support_1_endpoint_invariance_norm_bound
    {d : ℕ} (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (φ : DomainL2 (centeredCube z0 r0 hr0)) (fc : SpatialCoordinates d → ℝ)
    (hφfc : (φ : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] fc)
    (ε ε' : ℝ) (_hε : 0 < ε) (hε'pos : 0 < ε')
    (hε'def : ε' = ε / (2 * Real.sqrt
      ((volume (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))).toReal)))
    (v : DomainL2 (centeredCube z0 r0 hr0)) (vc w : SpatialCoordinates d → ℝ)
    (hveq : (v : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] vc)
    (rk : ℝ)
    (hbnd : ∀ x ∈ closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)),
      |vc x - w x| ≤ rk)
    (hg : ∀ x : SpatialCoordinates d, |w x - fc x| ≤ ε') (hkbound : rk ≤ ε') :
    ‖v - φ‖ ≤ ε := by
  set Q : Set (SpatialCoordinates d) := (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))
    with hQdef
  have hvolQ : volume Q = ENNReal.ofReal (r0 ^ d) := centeredCube_volume z0 hr0
  have hvolQne : volume Q ≠ ⊤ := by rw [hvolQ]; exact ENNReal.ofReal_ne_top
  have hptbound : ∀ x ∈ Q, |vc x - fc x| ≤ 2 * ε' := by
    intro x hx
    have h1 : |vc x - w x| ≤ rk := hbnd x (subset_closure hx)
    have h2 : |w x - fc x| ≤ ε' := hg x
    have := abs_sub_le (vc x) (w x) (fc x)
    linarith [hkbound]
  have hae : ∀ᵐ x ∂(volume.restrict Q), ‖(v - φ) x‖ ≤ 2 * ε' := by
    have hbase : ∀ᵐ x ∂(volume.restrict Q), x ∈ Q ∧
        v x = vc x ∧ (φ : SpatialCoordinates d → ℝ) x = fc x := by
      filter_upwards [ae_restrict_mem (centeredCube z0 r0 hr0).isOpen.measurableSet,
        hveq, hφfc] with x hx h1 h2 using ⟨hx, h1, h2⟩
    filter_upwards [hbase, Lp.coeFn_sub v φ] with x hx hsub
    rw [hsub]
    show ‖v x - φ x‖ ≤ 2 * ε'
    rw [hx.2.1, hx.2.2, Real.norm_eq_abs]
    exact hptbound x hx.1
  have hL2 : ‖v - φ‖ ≤ (2 * ε') * Real.sqrt ((volume.restrict Q Set.univ).toReal) := by
    refine _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.norm_le_of_ae_indicator_bound MeasurableSet.univ
      (by rw [MeasureTheory.Measure.restrict_apply_univ]; exact hvolQne) (by positivity) ?_
    filter_upwards [hae] with x hx
    rwa [Set.indicator_univ]
  rw [MeasureTheory.Measure.restrict_apply_univ] at hL2
  have hsqrtne : Real.sqrt ((volume Q).toReal) ≠ 0 := by
    rw [hvolQ, ENNReal.toReal_ofReal (by positivity)]
    exact (Real.sqrt_pos.mpr (by positivity)).ne'
  have hfinal : (2 * ε') * Real.sqrt ((volume Q).toReal) = ε := by
    have hgoal : (2 * ε') * Real.sqrt ((volume Q).toReal)
        = ε' * (2 * Real.sqrt ((volume Q).toReal)) := by ring
    rw [hgoal, hε'def]
    exact div_mul_cancel₀ ε (mul_ne_zero two_ne_zero hsqrtne)
  linarith [hL2, hfinal.symm.le, hfinal.le]

theorem aux_lem_endpoints_support_1_endpoint_invariance_fc_setup
    {d : ℕ} (hd : 2 ≤ d)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0))
    (G : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N : ℕ → ℕ)
    (hbundle : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 S G N)
    (fc : SpatialCoordinates d → ℝ) (hfcSmooth : ContDiff ℝ (⊤ : ℕ∞) fc)
    (hfcSupp : HasCompactSupport fc)
    (hfcTsupp : tsupport fc ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (D : Submodule ℚ (DomainL2 (centeredCube z0 r0 hr0)))
      (phi : D → Homogenization.H1Function (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)))
      (alpha : ℝ),
      (∀ f : D, ∃ Cphi : ℝ, 0 ≤ Cphi ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        ∃ vN : ℕ → S.space, ∃ vcN : ℕ → SpatialCoordinates d → ℝ,
        ∃ Kset : Set (SpatialCoordinates d),
          IsCompact Kset ∧ Kset ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ∧
          ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
            (vN n).val.1
              =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] vcN n ∧
            ContinuousOn (vcN n) (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) ∧
            (∀ x ∈ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) \ Kset, vcN n x = 0) ∧
            _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
              (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (vcN n) ∧
            _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
              (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (vcN n) ≤ M ∧
            responseForm S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z0 hr0)
              (vN n) (vN n) ≤ M ∧
            ∀ x ∈ closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)),
              |vcN n x - (phi f).toFun x| ≤ Cphi * (r0 / (3 : ℝ) ^ k)) ∧
      ∃ (ε' : ℝ), (ε' = ε / (2 * Real.sqrt
        ((volume (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))).toReal)) ∧ 0 < ε') ∧
      ∃ (g : D), ∀ x : SpatialCoordinates d, |(phi g).toFun x - fc x| ≤ ε' := by
  obtain ⟨D, phi, alpha, _hDdense, _hPhi, hFiniteMesh, hsmooth⟩ :=
    aux_lem_endpoints_support_1_endpoint_invariance_bounds_side_fields hd model H om z0 r0 hr0 S G N hbundle
  have hvolQ : volume (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))
      = ENNReal.ofReal (r0 ^ d) := centeredCube_volume z0 hr0
  have hvolQtoReal : (volume (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))).toReal
      = r0 ^ d := by rw [hvolQ, ENNReal.toReal_ofReal (by positivity)]
  have hsqrtpos : 0 < Real.sqrt
      ((volume (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))).toReal) := by
    rw [hvolQtoReal]; exact Real.sqrt_pos.mpr (by positivity)
  let ε' : ℝ := ε / (2 * Real.sqrt
    ((volume (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))).toReal))
  have hε'def : ε' = ε / (2 * Real.sqrt
      ((volume (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))).toReal)) := rfl
  have hε'pos : 0 < ε' := div_pos hε (by linarith [hsqrtpos])
  obtain ⟨g, hg⟩ := hsmooth fc hfcSmooth.continuous hfcSupp hfcTsupp ε' hε'pos
  exact ⟨D, phi, alpha, hFiniteMesh, ε', ⟨hε'def, hε'pos⟩, g, hg⟩

theorem aux_lem_endpoints_support_1_endpoint_invariance_hmesh_of_bounds_side
    {d : ℕ} (hd : 2 ≤ d)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0))
    (G : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N : ℕ → ℕ)
    (hbundle : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 S G N) :
    ∀ φ : DomainL2 (centeredCube z0 r0 hr0),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ∧
        (φ : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] fc) →
      ∀ ε : ℝ, 0 < ε → ∃ w : ℕ → S.space, ∃ C : ℝ,
        (∀ n : ℕ, responseForm S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z0 hr0)
          (w n) (w n) ≤ C) ∧
        (∀ n : ℕ, ‖(w n).val.1 - φ‖ ≤ ε) := by
  intro φ hφex ε hε
  obtain ⟨fc, hfcSmooth, hfcSupp, hfcTsupp, hφfc⟩ := hφex
  obtain ⟨D, phi, alpha, hFiniteMesh, ε', ⟨hε'def, hε'pos⟩, g, hg⟩ :=
    aux_lem_endpoints_support_1_endpoint_invariance_fc_setup hd model H om z0 r0 hr0 S G N hbundle
      fc hfcSmooth hfcSupp hfcTsupp ε hε
  clear hbundle hfcSmooth hfcSupp hfcTsupp
  obtain ⟨Cphi, hCphi0, k0, hFM⟩ := hFiniteMesh g
  clear hFiniteMesh
  have hk : ∃ k : ℕ, k0 ≤ k ∧ Cphi * (r0 / (3 : ℝ) ^ k) ≤ ε' :=
    aux_lem_endpoints_support_1_endpoint_invariance_hk_of_Cphi Cphi hCphi0 k0 r0 hr0 ε' hε'pos
  obtain ⟨k, hk0k, hkbound⟩ := hk
  clear hCphi0
  obtain ⟨vN, vcN, M, hvNeqAll, hrespAll, hbndAll⟩ :=
    aux_lem_endpoints_support_1_endpoint_invariance_hFM_fields hd model H om z0 r0 hr0 S N D phi alpha g Cphi k0
      k hk0k hFM
  refine ⟨vN, M, hrespAll, fun n => ?_⟩
  have hvNeq := hvNeqAll n
  have hbnd := hbndAll n
  exact aux_lem_endpoints_support_1_endpoint_invariance_norm_bound z0 r0 hr0 φ fc hφfc ε ε' hε hε'pos hε'def
    (vN n).val.1 (vcN n) (phi g).toFun hvNeq (Cphi * (r0 / (3 : ℝ) ^ k)) hbnd hg hkbound

theorem aux_lem_endpoints_support_1_regularity_instance_killed_gdense
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hGmem : ∀ f : DomainL2 (centeredCube z r hr), G f ∈ E.toClosedForm.domain)
    (hRange : ∀ v ∈ E.toClosedForm.domain, ∀ ε : ℝ, 0 < ε →
      ∃ f0 : DomainL2 (centeredCube z r hr), E.toClosedForm.energyNormSq (v - G f0) < ε)
    (hGbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : DomainL2 (centeredCube z r hr),
      E.toClosedForm.energyNormSq (G f) ≤ C * ‖f‖ ^ 2)
    (D : Submodule ℚ (DomainL2 (centeredCube z r hr)))
    (hDdense : Dense (D : Set (DomainL2 (centeredCube z r hr)))) :
    ∀ v ∈ E.toClosedForm.domain, ∀ ε : ℝ, 0 < ε →
      ∃ f : D, E.toClosedForm.energyNormSq (v - G f.val) < ε := by
  obtain ⟨C, hC0, hGbound⟩ := hGbound
  intro v hv ε hε
  obtain ⟨f0, hf0⟩ := hRange v hv (ε / 16) (by positivity)
  set δ : ℝ := Real.sqrt (ε / 16) / (Real.sqrt C + 1) with hδdef
  have hδpos : 0 < δ := by positivity
  obtain ⟨f', hf'D, hf'dist⟩ :=
    Metric.mem_closure_iff.mp (hDdense f0) δ hδpos
  refine ⟨⟨f', hf'D⟩, ?_⟩
  have hlin : G f0 - G f' = G (f0 - f') := (G.map_sub f0 f').symm
  have hCsq : C ≤ (Real.sqrt C + 1) ^ 2 := by
    nlinarith [Real.sq_sqrt hC0, Real.sqrt_nonneg C]
  have hδsq : δ ^ 2 = (ε / 16) / (Real.sqrt C + 1) ^ 2 := by
    rw [hδdef, div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ ε / 16 by positivity)]
  have hδsq_eq : δ ^ 2 * (Real.sqrt C + 1) ^ 2 = ε / 16 := by
    rw [hδsq]
    have hne : (Real.sqrt C + 1) ^ 2 ≠ 0 := by positivity
    field_simp
  have hCδsq : C * δ ^ 2 ≤ ε / 16 := by
    rw [← hδsq_eq]
    nlinarith [mul_nonneg (sub_nonneg.mpr hCsq) (sq_nonneg δ)]
  have hbound2 : E.toClosedForm.energyNormSq (G f0 - G f') ≤ ε / 16 := by
    rw [hlin]
    calc E.toClosedForm.energyNormSq (G (f0 - f'))
        ≤ C * ‖f0 - f'‖ ^ 2 := hGbound (f0 - f')
      _ ≤ C * δ ^ 2 := by
          gcongr
          rw [← dist_eq_norm]
          exact hf'dist.le
      _ ≤ ε / 16 := hCδsq
  have htri := E.toClosedForm.sqrt_energyNormSq_sub_le hv (hGmem f0) (hGmem f')
  have h1 : Real.sqrt (E.toClosedForm.energyNormSq (v - G f0)) < Real.sqrt (ε / 16) :=
    Real.sqrt_lt_sqrt (E.toClosedForm.energyNormSq_nonneg
      (E.toClosedForm.domain.sub_mem hv (hGmem f0))) hf0
  have h2 : Real.sqrt (E.toClosedForm.energyNormSq (G f0 - G f')) ≤ Real.sqrt (ε / 16) :=
    Real.sqrt_le_sqrt hbound2
  have hsum := add_lt_add_of_lt_of_le h1 h2
  have hfinal : Real.sqrt (E.toClosedForm.energyNormSq (v - G f')) <
      Real.sqrt (ε / 16) + Real.sqrt (ε / 16) := lt_of_le_of_lt htri hsum
  have hle : Real.sqrt (ε / 16) + Real.sqrt (ε / 16) ≤ Real.sqrt ε := by
    have heq : Real.sqrt (ε / 16) + Real.sqrt (ε / 16) = Real.sqrt (ε / 4) := by
      rw [show ε / 16 = (ε / 4) * (1 / 4 : ℝ) by ring, Real.sqrt_mul (by positivity),
        show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    rw [heq]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlt : Real.sqrt (E.toClosedForm.energyNormSq (v - G f')) < Real.sqrt ε :=
    lt_of_lt_of_le hfinal hle
  have hnn : 0 ≤ E.toClosedForm.energyNormSq (v - G f') :=
    E.toClosedForm.energyNormSq_nonneg (E.toClosedForm.domain.sub_mem hv (hGmem f'))
  have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).2 hlt
  simpa only [Real.sq_sqrt hnn, Real.sq_sqrt hε.le] using hsq

theorem aux_lem_endpoints_support_1_regularity_instance_killed
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (N : ℕ → ℕ)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ v : DomainL2 (centeredCube z r hr),
      E.toClosedForm.energy v = limitFormEnergy G v)
    (hGmem : ∀ f : DomainL2 (centeredCube z r hr), G f ∈ E.toClosedForm.domain)
    (hLower : ∀ (vN : ℕ → S.space) (v : DomainL2 (centeredCube z r hr)),
      (∀ f : DomainL2 (centeredCube z r hr),
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
      E.toClosedForm.energy v ≤
        liminf (fun n => ((responseForm S
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z hr) (vN n) (vN n) : ℝ) :
            EReal)) atTop)
    (hbundle : aux_in_represented_bounds_side d hd model H om z r hr S G N)
    (hRange : ∀ v ∈ E.toClosedForm.domain, ∀ ε : ℝ, 0 < ε →
      ∃ f0 : DomainL2 (centeredCube z r hr), E.toClosedForm.energyNormSq (v - G f0) < ε)
    (hGbound : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ f : DomainL2 (centeredCube z r hr),
      E.toClosedForm.energyNormSq (G f) ≤ Cb * ‖f‖ ^ 2) :
    (∃ C : Set (DomainL2 (centeredCube z r hr)),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
        (centeredCube z r hr : Set (SpatialCoordinates d)) C) ∧
    _root_.SubdiffusiveProcess.DirichletForm.IsRegular E.toClosedForm := by
  obtain ⟨KN, hKN, Kstar, hKstar, hfrac, hcoercive, hInterp, t, ht, htd, hcutoffs,
    D, hDcount, hDdense, phi, hPhi, alpha, eta, halpha_gt, halpha_lt, heta_pos, heta_lt,
    u, uc, hU, hUrep, hUconv, hUholder, rho, hrho, chi, hChi, w, hW, hCollarError,
    hFiniteMesh, hsmooth, -⟩ := hbundle
  have : Countable D := hDcount
  have hGdense := aux_lem_endpoints_support_1_regularity_instance_killed_gdense d z r hr G E hGmem hRange hGbound D hDdense
  exact prop_regularity d hd z r hr S hS
    (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N n) z hr)
    E G hE hGmem hLower D hDdense phi hPhi hGdense
    alpha eta t halpha_gt halpha_lt heta_pos ht heta_lt
    u uc hU hUrep hUconv hUholder rho hrho chi hChi w hW hCollarError hFiniteMesh hsmooth

theorem aux_lem_endpoints_support_1_hregularity_supply
    {d : ℕ} (hd : 2 ≤ d)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (Sspace0 : ResponseSpace (centeredCube z0 r0 hr0))
    (G0 : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N0 : ℕ → ℕ)
    (hbundle0 : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 Sspace0 G0 N0) :
    ∃ K : ℝ, 0 < K ∧
      (∀ (n : ℕ) (v : Sspace0.space),
        cubeFractionalL2Seminorm hd z0 r0 hr0 _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
            (fun _ : Fin 1 => v.val.1) < ⊤ ∧
        ‖v.val.1‖ ^ 2 + volume.real (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) *
            ((cubeFractionalL2Seminorm hd z0 r0 hr0 _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
                (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 ≤
          K * responseForm Sspace0
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N0 n) z0 hr0) v v) ∧
      ∃ D : Submodule ℚ (DomainL2 (centeredCube z0 r0 hr0)),
        (D : Set (DomainL2 (centeredCube z0 r0 hr0))).Countable ∧
        Dense (D : Set (DomainL2 (centeredCube z0 r0 hr0))) ∧
        (∀ f : D, ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧
          HasCompactSupport fc ∧
          tsupport fc ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ∧
          (f.val : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] fc) ∧
      CubeFractionalInterpolationInput d hd := by
  rcases hbundle0 with ⟨KN, hKN, Kstar, hKstar, hfrac, hcoercive, hInterp, hrest⟩
  rcases hrest with ⟨t, ht, htd, hcutoffs,
    D, hDcountRaw, hDdense, phi, hPhi, alpha, eta, halpha_gt, halpha_lt, heta_pos, heta_lt,
    u, uc, hU, hUrep, hUconv, hUholder, rho, hrho, chi, hChi, w, hW, hCollarError,
    hFiniteMesh, hsmooth, -⟩
  have : Countable D := hDcountRaw
  have hDcountSet : Countable (D : Set (DomainL2 (centeredCube z0 r0 hr0))) := hDcountRaw
  refine ⟨max Kstar 1, lt_of_lt_of_le one_pos (le_max_right Kstar 1), fun n v => ⟨hfrac v, ?_⟩,
    D, Set.countable_coe_iff.mp hDcountSet, hDdense, fun f => ?_, hInterp⟩
  · have h1 := hcoercive n v
    have h2 : KN n ≤ max Kstar 1 := (hKstar n).trans (le_max_left Kstar 1)
    have h3 := responseForm_nonneg Sspace0
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N0 n) z0 hr0) v
    calc ‖v.val.1‖ ^ 2 + volume.real (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) *
            ((cubeFractionalL2Seminorm hd z0 r0 hr0 _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
                (fun _ : Fin 1 => v.val.1)).toReal) ^ 2
        ≤ KN n * responseForm Sspace0
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N0 n) z0 hr0) v v := h1
      _ ≤ max Kstar 1 * responseForm Sspace0
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (N0 n) z0 hr0) v v :=
          mul_le_mul_of_nonneg_right h2 h3
  · obtain ⟨hC1, hC2, hC3, hC4⟩ := hPhi f
    refine ⟨(phi f).toFun, hC1, hC2, hC3, ?_⟩
    have hb := sobolevDataOfH1_fst_coeFn (phi f)
    rwa [hC4] at hb

theorem aux_lem_endpoints_support_1_hregularity_hRange_of_root
    {d : ℕ} {z0 : SpatialCoordinates d} {r0 : ℝ} {hr0 : 0 < r0}
    (G0 Rroot : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (EForm : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))))
    (hE : ∀ v : DomainL2 (centeredCube z0 r0 hr0),
      EForm.toClosedForm.energy v = limitFormEnergy G0 v)
    (hSymmC : ∀ x y : DomainL2 (centeredCube z0 r0 hr0), inner ℝ (G0 x) y = inner ℝ x (G0 y))
    (hRsymm : ∀ x y : DomainL2 (centeredCube z0 r0 hr0), inner ℝ (Rroot x) y = inner ℝ x (Rroot y))
    (hRcomp : Rroot.comp Rroot = G0)
    (hRinj : Function.Injective Rroot)
    (hRdom : limitFormDomain G0 = Set.range Rroot)
    (hGmem : ∀ f : DomainL2 (centeredCube z0 r0 hr0), G0 f ∈ EForm.toClosedForm.domain)
    (hEdomIff : ∀ v0 : DomainL2 (centeredCube z0 r0 hr0),
      v0 ∈ EForm.toClosedForm.domain ↔ v0 ∈ limitFormDomain G0) :
    ∀ v ∈ EForm.toClosedForm.domain, ∀ ε : ℝ, 0 < ε →
      ∃ f0 : DomainL2 (centeredCube z0 r0 hr0),
        EForm.toClosedForm.energyNormSq (v - G0 f0) < ε := by
  have hdenseR : Dense (Set.range Rroot : Set (DomainL2 (centeredCube z0 r0 hr0))) := by
    have h := aux_prop_killed_inverse_dirichlet_form_root_dense Rroot hRsymm hRinj
    rw [LinearMap.coe_range] at h
    simpa using h
  intro v hv ε hε
  have hvdom : v ∈ limitFormDomain G0 := (hEdomIff v).mp hv
  rw [hRdom] at hvdom
  obtain ⟨wv, hwv⟩ := hvdom
  set δ : ℝ := Real.sqrt (ε / (2 * (1 + ‖Rroot‖ ^ 2))) with hδdef
  have hδpos : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨y, hyR, hydist⟩ := Metric.mem_closure_iff.mp (hdenseR wv) δ hδpos
  obtain ⟨f0, hf0⟩ := hyR
  refine ⟨f0, ?_⟩
  have hGf0 : G0 f0 = Rroot (Rroot f0) := by
    rw [← ContinuousLinearMap.comp_apply, hRcomp]
  have hnorm : ‖wv - Rroot f0‖ < δ := by
    rw [← hf0] at hydist; rwa [dist_eq_norm] at hydist
  have hveq : v - G0 f0 = Rroot (wv - Rroot f0) := by
    rw [map_sub, hwv, hGf0]
  have hmemsub : v - G0 f0 ∈ EForm.toClosedForm.domain :=
    EForm.toClosedForm.domain.sub_mem hv (hGmem f0)
  have hval : EForm.toClosedForm.energy (v - G0 f0) =
      (EForm.toClosedForm.form (v - G0 f0) (v - G0 f0) : EReal) :=
    EForm.toClosedForm.energy_of_mem hmemsub
  have hdual := aux_prop_killed_inverse_dirichlet_form_dual_energy_root_range G0 Rroot
    hSymmC hRsymm hRcomp hRinj (wv - Rroot f0)
  rw [real_inner_self_eq_norm_sq] at hdual
  have heq2 : limitFormEnergy G0 (Rroot (wv - Rroot f0)) =
      ((‖wv - Rroot f0‖ ^ 2 : ℝ) : EReal) := hdual
  have hchain : (EForm.toClosedForm.form (v - G0 f0) (v - G0 f0) : EReal) =
      ((‖wv - Rroot f0‖ ^ 2 : ℝ) : EReal) := by
    rw [← hval, hE, hveq]; exact heq2
  have hformeq : EForm.toClosedForm.form (v - G0 f0) (v - G0 f0) = ‖wv - Rroot f0‖ ^ 2 := by
    exact_mod_cast hchain
  have hnormle : ‖v - G0 f0‖ ≤ ‖Rroot‖ * ‖wv - Rroot f0‖ := by
    rw [hveq]; exact Rroot.le_opNorm _
  have h1 : ‖v - G0 f0‖ ^ 2 ≤ ‖Rroot‖ ^ 2 * ‖wv - Rroot f0‖ ^ 2 := by
    have hh := mul_self_le_mul_self (norm_nonneg _) hnormle
    nlinarith [hh]
  have hsqlt : ‖wv - Rroot f0‖ ^ 2 < δ ^ 2 := by
    have hh := mul_self_lt_mul_self (norm_nonneg _) hnorm
    nlinarith [hh]
  have hδsq2 : 2 * ((1 + ‖Rroot‖ ^ 2) * δ ^ 2) = ε := by
    rw [← mul_assoc, hδdef, Real.sq_sqrt (by positivity), mul_comm]
    exact div_mul_cancel₀ ε (by positivity)
  have hhalf : (1 + ‖Rroot‖ ^ 2) * δ ^ 2 = ε / 2 := by linarith [hδsq2]
  have hstep : (1 + ‖Rroot‖ ^ 2) * ‖wv - Rroot f0‖ ^ 2 < (1 + ‖Rroot‖ ^ 2) * δ ^ 2 :=
    mul_lt_mul_of_pos_left hsqlt (by positivity)
  show EForm.toClosedForm.form (v - G0 f0) (v - G0 f0) + ‖v - G0 f0‖ ^ 2 < ε
  rw [hformeq]
  nlinarith [h1, hstep, hhalf]

theorem aux_lem_endpoints_support_1_hregularity_hGbound_of_root
    {d : ℕ} {z0 : SpatialCoordinates d} {r0 : ℝ} {hr0 : 0 < r0}
    (G0 Rroot : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (EForm : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))))
    (hE : ∀ v : DomainL2 (centeredCube z0 r0 hr0),
      EForm.toClosedForm.energy v = limitFormEnergy G0 v)
    (hSymmC : ∀ x y : DomainL2 (centeredCube z0 r0 hr0), inner ℝ (G0 x) y = inner ℝ x (G0 y))
    (hRsymm : ∀ x y : DomainL2 (centeredCube z0 r0 hr0), inner ℝ (Rroot x) y = inner ℝ x (Rroot y))
    (hRcomp : Rroot.comp Rroot = G0)
    (hRinj : Function.Injective Rroot)
    (hGmem : ∀ f : DomainL2 (centeredCube z0 r0 hr0), G0 f ∈ EForm.toClosedForm.domain) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ f : DomainL2 (centeredCube z0 r0 hr0),
      EForm.toClosedForm.energyNormSq (G0 f) ≤ Cb * ‖f‖ ^ 2 := by
  refine ⟨‖Rroot‖ ^ 2 + ‖G0‖ ^ 2, by positivity, fun f => ?_⟩
  have hmemf : G0 f ∈ EForm.toClosedForm.domain := hGmem f
  have hGf : G0 f = Rroot (Rroot f) := by rw [← ContinuousLinearMap.comp_apply, hRcomp]
  have hdual2 := aux_prop_killed_inverse_dirichlet_form_dual_energy_root_range G0 Rroot
    hSymmC hRsymm hRcomp hRinj (Rroot f)
  rw [real_inner_self_eq_norm_sq] at hdual2
  have heq3 : limitFormEnergy G0 (G0 f) = ((‖Rroot f‖ ^ 2 : ℝ) : EReal) := by
    rw [hGf]; exact hdual2
  have hval2 : EForm.toClosedForm.energy (G0 f) =
      (EForm.toClosedForm.form (G0 f) (G0 f) : EReal) :=
    EForm.toClosedForm.energy_of_mem hmemf
  have hchain2 : (EForm.toClosedForm.form (G0 f) (G0 f) : EReal) =
      ((‖Rroot f‖ ^ 2 : ℝ) : EReal) := by
    rw [← hval2, hE]; exact heq3
  have hformeq2 : EForm.toClosedForm.form (G0 f) (G0 f) = ‖Rroot f‖ ^ 2 := by
    exact_mod_cast hchain2
  show EForm.toClosedForm.form (G0 f) (G0 f) + ‖G0 f‖ ^ 2 ≤
      (‖Rroot‖ ^ 2 + ‖G0‖ ^ 2) * ‖f‖ ^ 2
  rw [hformeq2]
  have h2 : ‖Rroot f‖ ≤ ‖Rroot‖ * ‖f‖ := Rroot.le_opNorm f
  have h3 : ‖G0 f‖ ≤ ‖G0‖ * ‖f‖ := G0.le_opNorm f
  have h2sq : ‖Rroot f‖ ^ 2 ≤ ‖Rroot‖ ^ 2 * ‖f‖ ^ 2 := by
    have hh := mul_self_le_mul_self (norm_nonneg (Rroot f)) h2
    nlinarith [hh]
  have h3sq : ‖G0 f‖ ^ 2 ≤ ‖G0‖ ^ 2 * ‖f‖ ^ 2 := by
    have hh := mul_self_le_mul_self (norm_nonneg (G0 f)) h3
    nlinarith [hh]
  nlinarith [h2sq, h3sq]

/-- Weak (ω-dependent sub-subsequence) form of the represented bounds, : at a.e. field and every catalogue cube, every strong limit of the cutoff responses
along `NE` (resp. `NF`) satisfies the represented bounds along SOME further subsequence
`NE ∘ σ` (σ chosen after `om`, `i`, `Glim`). Weaker than the fixed-subsequence form. -/
def aux_lem_endpoints_bounds_pointwise
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) : Prop :=
  ∃ G : Set (BilateralField d), MeasurableSet G ∧ (chaosSampleLaw model).toMeasure Gᶜ = 0 ∧
    ∀ om ∈ G, ∀ i : ℕ,
      (∀ Glim : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)),
        (∀ f : DomainL2 (centeredCube (z i) (r i) (hr i)),
          Tendsto (fun n => (responseSolution (Sspace i)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (NE n) (z i) (hr i))
            ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1)
            atTop (𝓝 (Glim f))) →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
          aux_in_represented_bounds_side d hd model H om (z i) (r i) (hr i) (Sspace i) Glim
            (NE ∘ σ)) ∧
      (∀ Glim : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)),
        (∀ f : DomainL2 (centeredCube (z i) (r i) (hr i)),
          Tendsto (fun n => (responseSolution (Sspace i)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om (NF n) (z i) (hr i))
            ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1)
            atTop (𝓝 (Glim f))) →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
          aux_in_represented_bounds_side d hd model H om (z i) (r i) (hr i) (Sspace i) Glim
            (NF ∘ σ))

/-- The weak represented bounds of the joint candidates: for a.e. field and every catalogue cube the limit
forms `GE`, `GF` satisfy the represented bounds along some further subsequences `NE ∘ σ`, `NF ∘ σ`. -/
def aux_lem_endpoints_support_1_represented_bounds_weak
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) : Prop :=
  ∀ᵐ om ∂P, ∀ i : ℕ,
    (∃ σ : ℕ → ℕ, StrictMono σ ∧
      aux_in_represented_bounds_side d hd model H (field om) (z i) (r i) (hr i)
        (Sspace i) (GE i om) (NE ∘ σ)) ∧
    (∃ σ : ℕ → ℕ, StrictMono σ ∧
      aux_in_represented_bounds_side d hd model H (field om) (z i) (r i) (hr i)
        (Sspace i) (GF i om) (NF ∘ σ))

theorem lem_endpoints_support_1
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {model : _root_.SubdiffusiveProcess.Model.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ i, 0 < r i}
    {Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i))}
    {NE NF : ℕ → ℕ}
    (hPW : aux_lem_endpoints_bounds_pointwise d hd model H z r hr Sspace NE NF)
    {GNc : (i : ℕ) → ℕ → BilateralField d →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i))}
    {GEc GFc : (i : ℕ) → BilateralField d →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i))}
    (hJointC : in_joint_extracted_candidates d model H (BilateralField d)
      (chaosSampleLaw model).toMeasure (fun om => om) z r hr Sspace GNc GEc GFc NE NF) :
    aux_lem_endpoints_support_1_represented_bounds_weak d hd model H (BilateralField d)
      (chaosSampleLaw model).toMeasure (fun om => om) z r hr Sspace GEc GFc NE NF := by
  obtain ⟨G, _hGmeas, hGcompl, hG⟩ := hPW
  have hae : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure, om ∈ G := by
    rw [ae_iff]
    simpa [compl_ofPred] using! hGcompl
  have hformula : ∀ i N (x : BilateralField d) f, GNc i N x f =
      (responseSolution (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H x N (z i) (hr i))
        ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1 :=
    hJointC.2.2.2.2.2.2.1
  have htendsto : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure, ∀ i,
      Tendsto (fun n => GNc i (NE n) om) atTop (𝓝 (GEc i om)) ∧
      Tendsto (fun n => GNc i (NF n) om) atTop (𝓝 (GFc i om)) :=
    hJointC.2.2.2.2.2.2.2
  filter_upwards [hae, htendsto] with om hom htends i
  refine ⟨?_, ?_⟩
  · apply (hG om hom i).1 (GEc i om)
    intro f
    have heval : Tendsto (fun n => GNc i (NE n) om f) atTop (𝓝 (GEc i om f)) :=
      ((ContinuousLinearMap.apply ℝ (DomainL2 (centeredCube (z i) (r i) (hr i))) f).continuous.tendsto
        (GEc i om)).comp (htends i).1
    simpa only [hformula i (NE _) om f] using heval
  · apply (hG om hom i).2 (GFc i om)
    intro f
    have heval : Tendsto (fun n => GNc i (NF n) om f) atTop (𝓝 (GFc i om f)) :=
      ((ContinuousLinearMap.apply ℝ (DomainL2 (centeredCube (z i) (r i) (hr i))) f).continuous.tendsto
        (GFc i om)).comp (htends i).2
    simpa only [hformula i (NF _) om f] using heval

end SubdiffusiveProcess.Paper
