module

public import SubdiffusiveProcess.Paper.prop_killed_inverse_spectral_square_root
public import SubdiffusiveProcess.Paper.prop_killed_inverse_dirichlet_form
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper




lemma aux_prop_killed_inverse_form_density_energy_bound
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (R : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hR : ∀ x y : DomainL2 Q,
      inner ℝ (R x) y = inner ℝ x (R y))
    (y f : DomainL2 Q) :
    limitFormEnergy (R.comp R) (R (y - R f)) ≤
      ((‖y - R f‖ ^ 2 : ℝ) : EReal) := by
  unfold limitFormEnergy
  refine iSup_le (fun g => ?_)
  have hrewrite₁ :
      inner ℝ g (R (y - R f)) =
        inner ℝ (R g) (y - R f) := by
    rw [← hR g (y - R f)]
  have hrewrite₂ :
      inner ℝ g ((R.comp R) g) = inner ℝ (R g) (R g) := by
    rw [ContinuousLinearMap.comp_apply, hR g (R g)]
  rw [hrewrite₁, hrewrite₂]
  have hsq : 0 ≤ ‖(y - R f) - R g‖ ^ 2 := sq_nonneg _
  rw [norm_sub_sq_real] at hsq
  rw [real_inner_comm (R g) (y - R f)] at hsq
  rw [real_inner_self_eq_norm_sq]
  exact EReal.coe_le_coe (by nlinarith)

lemma aux_prop_killed_inverse_form_density_range_closure
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (R : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hR : ∀ x y : DomainL2 Q,
      inner ℝ (R x) y = inner ℝ x (R y)) :
    (↑(LinearMap.range R.toLinearMap) : Set (DomainL2 Q)) ⊆
      closure (↑(LinearMap.range (R.comp R).toLinearMap) : Set (DomainL2 Q)) := by
  let K : Submodule ℝ (DomainL2 Q) := LinearMap.range R.toLinearMap
  have horth : (LinearMap.range (R.comp R).toLinearMap : Submodule ℝ (DomainL2 Q))ᗮ ≤
      (LinearMap.range R.toLinearMap : Submodule ℝ (DomainL2 Q))ᗮ := by
    intro z hz
    rw [Submodule.mem_orthogonal]
    intro v hv
    obtain ⟨x, rfl⟩ := hv
    have hGz : R (R z) = 0 := by
      apply ext_inner_left ℝ
      intro w
      have hw : inner ℝ (R (R w)) z = 0 := by
        apply hz
        exact ⟨w, rfl⟩
      have hw' : inner ℝ (R w) (R z) = 0 := by
        rw [← hR (R w) z]
        exact hw
      calc
        inner ℝ w (R (R z)) = inner ℝ (R w) (R z) := (hR w (R z)).symm
        _ = 0 := hw'
        _ = inner ℝ w 0 := by simp
    have hRz : inner ℝ (R z) (R z) = 0 := by
      calc
        inner ℝ (R z) (R z) = inner ℝ z (R (R z)) := hR z (R z)
        _ = 0 := by simp [hGz]
    have hn : ‖R z‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, hRz]
    have hRz0 : R z = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    change inner ℝ (R x) z = 0
    rw [hR x z, hRz0]
    simp
  have hdouble :
      (LinearMap.range R.toLinearMap : Submodule ℝ (DomainL2 Q))ᗮᗮ ≤
        (LinearMap.range (R.comp R).toLinearMap : Submodule ℝ (DomainL2 Q))ᗮᗮ :=
    Submodule.orthogonal_le horth
  have hrange :
      (LinearMap.range R.toLinearMap : Submodule ℝ (DomainL2 Q)) ≤
        (LinearMap.range (R.comp R).toLinearMap : Submodule ℝ (DomainL2 Q))ᗮᗮ :=
    (Submodule.le_orthogonal_orthogonal _).trans hdouble
  intro u hu
  have hu' : u ∈ (LinearMap.range R.toLinearMap : Submodule ℝ (DomainL2 Q)) := hu
  have hu'' := hrange hu'
  rw [Submodule.orthogonal_orthogonal_eq_closure] at hu''
  exact hu''

theorem prop_killed_inverse_form_density
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hroot : ∃ Rroot : DomainL2 Q →L[ℝ] DomainL2 Q,
      (∀ x y : DomainL2 Q,
        inner ℝ (Rroot x) y = inner ℝ x (Rroot y)) ∧
      (∀ x : DomainL2 Q, 0 ≤ inner ℝ x (Rroot x)) ∧
      Rroot.comp Rroot = G ∧ limitFormDomain G = Set.range Rroot)
    (EForm : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (Q : Set (SpatialCoordinates d))))
    (_hEForm : ∀ w : DomainL2 Q,
      EForm.toClosedForm.energy w = limitFormEnergy G w)
    (_hHNC : _root_.SubdiffusiveProcess.DirichletForm.HasNormalContractions EForm)
    (D : Submodule ℚ (DomainL2 Q))
    (_hDcount : (D : Set (DomainL2 Q)).Countable)
    (hDdense : Dense (D : Set (DomainL2 Q)))
    (hDsmooth : ∀ f : D,
      ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧
        HasCompactSupport fc ∧
        tsupport fc ⊆ (Q : Set (SpatialCoordinates d)) ∧
        (f.val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] fc) :
    ∀ u ∈ limitFormDomain G, ∀ ε : ℝ, 0 < ε →
      ∃ f : DomainL2 Q,
        (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧
          HasCompactSupport fc ∧ tsupport fc ⊆ (Q : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] fc) ∧
        ‖u - G f‖ ≤ ε ∧ limitFormEnergy G (u - G f) ≤ ((ε : ℝ) : EReal) := by
  intro u hu ε hε
  obtain ⟨R, hRsym, hRpos, hRG, hdom⟩ := hroot
  have huR : u ∈ Set.range R := by
    rw [← hdom]
    exact hu
  obtain ⟨x, hx⟩ := huR
  let K : Submodule ℝ (DomainL2 Q) := (LinearMap.range R.toLinearMap).topologicalClosure
  obtain ⟨y, hyK, z, hzK, hxdec⟩ :=
    Submodule.exists_add_mem_mem_orthogonal (K := K) x
  have hzR : z ∈ (LinearMap.range R.toLinearMap : Submodule ℝ (DomainL2 Q))ᗮ := by
    rw [← Submodule.orthogonal_closure]
    exact hzK
  have hRzG : R z = 0 := by
    apply ext_inner_left ℝ
    intro w
    have hw : inner ℝ (R w) z = 0 := by
      apply hzR
      exact ⟨w, rfl⟩
    calc
      inner ℝ w (R z) = inner ℝ (R w) z := (hRsym w z).symm
      _ = 0 := hw
      _ = inner ℝ w 0 := by simp
  have hRy : R y = u := by
    calc
      R y = R (y + z) := by rw [map_add, hRzG, add_zero]
      _ = R x := by rw [← hxdec]
      _ = u := hx
  have hycl : y ∈ closure (↑(LinearMap.range R.toLinearMap) : Set (DomainL2 Q)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hyK
  have hRimage :
      (↑(LinearMap.range R.toLinearMap) : Set (DomainL2 Q)) ⊆
        closure (R '' (D : Set (DomainL2 Q))) := by
    exact R.continuous.range_subset_closure_image_dense hDdense
  have hyimage : y ∈ closure (R '' (D : Set (DomainL2 Q))) := by
    exact closure_minimal hRimage isClosed_closure hycl
  let δ : ℝ := min 1 (ε / (‖R‖ + 1))
  have hRnorm : 0 ≤ ‖R‖ := norm_nonneg _
  have hden : 0 < ‖R‖ + 1 := by linarith
  have hratio : 0 < ε / (‖R‖ + 1) := div_pos hε hden
  have hδpos : 0 < δ := lt_min (by norm_num) hratio
  obtain ⟨v, ⟨f, hfD, rfl⟩, hv⟩ :=
    Metric.mem_closure_iff.1 hyimage δ hδpos
  let fD : D := ⟨f, hfD⟩
  have hres : ‖y - R f‖ < δ := by
    simpa [dist_eq_norm] using hv
  have hδone : δ ≤ 1 := min_le_left _ _
  have hratio_le : ε / (‖R‖ + 1) ≤ ε := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hδε : δ ≤ ε := (min_le_right _ _).trans hratio_le
  have hres_sq : ‖y - R f‖ ^ 2 ≤ ε := by
    have hres_nonneg : 0 ≤ ‖y - R f‖ := norm_nonneg _
    have hres_le : ‖y - R f‖ ≤ δ := le_of_lt hres
    have hres_sq_le : ‖y - R f‖ ^ 2 ≤ δ ^ 2 :=
      (sq_le_sq₀ hres_nonneg (le_of_lt hδpos)).2 hres_le
    have hδ_sq : δ ^ 2 ≤ δ := by
      have h := mul_le_mul_of_nonneg_left hδone (le_of_lt hδpos)
      simpa [pow_two] using h
    exact hres_sq_le.trans (hδ_sq.trans hδε)
  have hnormprod : ‖R‖ * ‖y - R f‖ ≤ ε := by
    have hres_le : ‖y - R f‖ ≤ δ := le_of_lt hres
    have hqnonneg : 0 ≤ ε / (‖R‖ + 1) := le_of_lt hratio
    have hprod₁ : ‖R‖ * ‖y - R f‖ ≤ ‖R‖ * δ :=
      mul_le_mul_of_nonneg_left hres_le hRnorm
    have hprod₂ : ‖R‖ * δ ≤ ‖R‖ * (ε / (‖R‖ + 1)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hRnorm
    have hprod₃ : ‖R‖ * (ε / (‖R‖ + 1)) ≤ ε := by
      calc
        ‖R‖ * (ε / (‖R‖ + 1)) ≤
            (‖R‖ + 1) * (ε / (‖R‖ + 1)) := by
              exact mul_le_mul_of_nonneg_right (by linarith) hqnonneg
        _ = ε := by field_simp
    exact hprod₁.trans (hprod₂.trans hprod₃)
  have hGf : G f = R (R f) := by
    rw [← hRG]
    rfl
  have hresidual : u - G f = R (y - R f) := by
    calc
      u - G f = R y - R (R f) := by rw [hRy, hGf]
      _ = R (y - R f) := by rw [map_sub]
  obtain ⟨fc, hfc, hfccompact, hfcsub, hfcae⟩ := hDsmooth fD
  refine ⟨f, ⟨fc, hfc, hfccompact, hfcsub, ?_⟩, ?_, ?_⟩
  · simpa [fD] using hfcae
  · rw [hresidual]
    exact (R.le_opNorm _).trans hnormprod
  · calc
      limitFormEnergy G (u - G f) =
          limitFormEnergy (R.comp R) (R (y - R f)) := by rw [hresidual, ← hRG]
      _ ≤ ((‖y - R f‖ ^ 2 : ℝ) : EReal) := by
        exact aux_prop_killed_inverse_form_density_energy_bound R hRsym y f
      _ ≤ ((ε : ℝ) : EReal) := EReal.coe_le_coe hres_sq

end SubdiffusiveProcess.Paper
