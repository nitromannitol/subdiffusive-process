module

public import SubdiffusiveProcess.Paper.lem_20_collar_family_smooth_collar
public import SubdiffusiveProcess.Lane2.MeshGluing

@[expose] public section

/-!
# Smooth collar representatives

Native H¹ and Sobolev-data packaging of the smooth collar used in the
collar-family construction. These are deterministic, axiom-clean helpers;
the harmonic cutoff and energy bounds remain separate obligations.
-/

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators Topology ContDiff

noncomputable section
namespace Paper

/-- Package the paper's smooth collar as a genuine `H1Function` on the fixed
cube, preserving the pointwise plateaux and zero gradient outside the collar. -/
theorem aux_lem_20_collar_family_smooth_H1
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ chi : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
      (∀ x,
        Metric.infDist x
            (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r →
          chi.toFun x = 0) ∧
      (∀ x,
        3 * r ≤ Metric.infDist x
            (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
          chi.toFun x = 1) ∧
      (∀ i : Fin d, ∀ x,
        3 * r < Metric.infDist x
            (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
          chi.grad x i = 0) := by
  rcases lem_20_collar_family_smooth_collar d hd z R hR r hr hr1 with
    ⟨theta, htheta_smooth, htheta_range, htheta_zero, htheta_one, htheta_deriv⟩
  have hgeom : IsOpenBoundedConvexDomain
      (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    lane2_isOpenBoundedConvexDomain_centeredCube z hR
  let chi : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain hgeom
      (htheta_smooth.of_le (by simp))
  refine ⟨chi, ?_, ?_, ?_, ?_⟩
  · intro x
    simpa [chi, H1Function.ofContDiffOnIsOpenBoundedConvexDomain] using! htheta_range x
  · intro x hx
    simpa [chi, H1Function.ofContDiffOnIsOpenBoundedConvexDomain] using! htheta_zero x hx
  · intro x hx
    simpa [chi, H1Function.ofContDiffOnIsOpenBoundedConvexDomain] using! htheta_one x hx
  · intro i x hx
    have hderiv := htheta_deriv x hx
    change (fderiv ℝ theta x) (basisVec i) = 0
    rw [hderiv]
    simp

/-- The same smooth collar's zero gradient, now in the exact Sobolev-data
component used by the collar-family conclusion. -/
theorem aux_lem_20_collar_family_smooth_data_gradient_zero
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ chi : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
      (∀ x,
        Metric.infDist x
            (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r →
          chi.toFun x = 0) ∧
      (∀ x,
        3 * r ≤ Metric.infDist x
            (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
          chi.toFun x = 1) ∧
      (∀ i : Fin d, ∀ᵐ x ∂volume.restrict
          (centeredCube z R hR : Set (SpatialCoordinates d)),
        3 * r < Metric.infDist x
            (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
          (((sobolevDataOfH1 chi).2 i : DomainL2
              (centeredCube z R hR)) : SpatialCoordinates d → ℝ) x = 0) := by
  rcases aux_lem_20_collar_family_smooth_H1 d hd z R hR r hr hr1 with
    ⟨chi, h_range, h_zero, h_one, h_grad_zero⟩
  refine ⟨chi, h_range, h_zero, h_one, ?_⟩
  intro i
  have h_ae := sobolevDataOfH1_snd_coeFn chi i
  filter_upwards [h_ae] with x hx_eq
  intro hx_inf
  rw [hx_eq]
  exact h_grad_zero i x hx_inf

/-- The smooth collar's value, support, and gradient clauses, expressed in
the exact Sobolev-data representatives used by the collar-family conclusion. -/
theorem aux_lem_20_collar_family_smooth_data_package
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ chi : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      (∀ᵐ x ∂volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d)),
        0 ≤ (((sobolevDataOfH1 chi).1 : DomainL2 (centeredCube z R hR)) :
          SpatialCoordinates d → ℝ) x ∧
        (((sobolevDataOfH1 chi).1 : DomainL2 (centeredCube z R hR)) :
          SpatialCoordinates d → ℝ) x ≤ 1) ∧
      (∀ᵐ x ∂volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d)),
        Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r →
          (((sobolevDataOfH1 chi).1 : DomainL2 (centeredCube z R hR)) :
            SpatialCoordinates d → ℝ) x = 0) ∧
      (∀ᵐ x ∂volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d)),
        3 * r ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
          (((sobolevDataOfH1 chi).1 : DomainL2 (centeredCube z R hR)) :
            SpatialCoordinates d → ℝ) x = 1) ∧
      (∀ i : Fin d, ∀ᵐ x ∂volume.restrict
          (centeredCube z R hR : Set (SpatialCoordinates d)),
        3 * r < Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
          (((sobolevDataOfH1 chi).2 i : DomainL2 (centeredCube z R hR)) :
            SpatialCoordinates d → ℝ) x = 0) := by
  obtain ⟨chi, hrange, hzero, hone, hgrad⟩ :=
    aux_lem_20_collar_family_smooth_data_gradient_zero d hd z R hR r hr hr1
  refine ⟨chi, ?_, ?_, ?_, hgrad⟩
  · have h := sobolevDataOfH1_fst_coeFn chi
    filter_upwards [h] with x hx
    rw [hx]
    exact hrange x
  · have h := sobolevDataOfH1_fst_coeFn chi
    filter_upwards [h] with x hx
    rw [hx]
    exact hzero x
  · have h := sobolevDataOfH1_fst_coeFn chi
    filter_upwards [h] with x hx
    rw [hx]
    exact hone x

/-- A smooth collar vanishing on a positive-width boundary strip belongs to
the actual killed response space once the represented-space identification is
used. This is only the membership step, not the harmonic energy estimate. -/
theorem aux_lem_20_collar_family_smooth_mem_response
    (d : ℕ) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hspace : S.space = killedSobolevGraph (centeredCube z R hR))
    (r : ℝ) (hr : 0 < r)
    (chi : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) chi.toFun)
    (hzero : ∀ x, Metric.infDist x
      (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r → chi.toFun x = 0) :
    ∃ v : S.space, v.val = sobolevDataOfH1 chi := by
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  have hclosed : IsClosed {x : SpatialCoordinates d |
      r ≤ Metric.infDist x Qᶜ} := by
    exact isClosed_le continuous_const (Metric.continuous_infDist_pt Qᶜ)
  have hsupp : Function.support chi.toFun ⊆
      {x : SpatialCoordinates d | r ≤ Metric.infDist x Qᶜ} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    by_contra h
    have hle : Metric.infDist x Qᶜ ≤ r := le_of_lt (lt_of_not_ge h)
    exact hx (hzero x hle)
  have htsupp : tsupport chi.toFun ⊆
      {x : SpatialCoordinates d | r ≤ Metric.infDist x Qᶜ} := by
    exact closure_minimal hsupp hclosed
  have hQ : tsupport chi.toFun ⊆ Q := by
    intro x hx
    have hxpos : 0 < Metric.infDist x Qᶜ := lt_of_lt_of_le hr (htsupp hx)
    have hnot : x ∉ Qᶜ := by
      intro hxc
      have hz : Metric.infDist x Qᶜ = 0 := Metric.infDist_zero_of_mem hxc
      exact (ne_of_gt hxpos) hz
    exact Set.notMem_compl_iff.mp hnot
  have hcompact : HasCompactSupport chi.toFun := by
    apply HasCompactSupport.of_support_subset_isCompact
      ((centeredCube_isBounded z hR).isCompact_closure)
    exact (subset_tsupport chi.toFun).trans (hQ.trans subset_closure)
  have hmem : sobolevDataOfH1 chi ∈ killedSobolevGraph (centeredCube z R hR) :=
    lane2_sobolevDataOfH1_mem_killed_of_test
      (centeredCube_isBounded z hR) chi hsmooth hcompact hQ
  exact ⟨⟨sobolevDataOfH1 chi, hspace ▸ hmem⟩, rfl⟩


end Paper




