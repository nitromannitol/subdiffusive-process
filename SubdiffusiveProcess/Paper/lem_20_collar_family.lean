-- paper label `mfd:lem-cutoffs` maps the named assembly obstacles to the
-- four existing collar children and the microscopic-majorant derivation.
module

public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.Main.CubeFractionalL2Norm
public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.cell_boundary_continuity
public import SubdiffusiveProcess.Paper.mesh_interpolator
public import SubdiffusiveProcess.Paper.lem_20_collar_family_mesh_scale
public import SubdiffusiveProcess.Paper.lem_20_collar_family_smooth_collar
public import SubdiffusiveProcess.Paper.lem_20_collar_family_cell_constant
public import SubdiffusiveProcess.Paper.lem_20_collar_family_response_congr
public import SubdiffusiveProcess.VariationalResponses.MeshGluing
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Paper.lem_extension

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

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
    isOpenBoundedConvexDomain_centeredCube z hR
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
    simp only [mem_ofPred_eq] at *
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
    sobolevDataOfH1_mem_killed_of_test
      (centeredCube_isBounded z hR) chi hsmooth hcompact hQ
  exact ⟨⟨sobolevDataOfH1 chi, hspace ▸ hmem⟩, rfl⟩

/-- Choose one mesh-comparison factor and inverse-power constant before every
real collar width. The selected triadic mesh is at most one eighth as wide. -/
theorem aux_lem_20_collar_family_scale_absorb
    (R eta : ℝ) (hR : 0 < R) (heta : 0 < eta) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ R ∧ c ≤ 1 / 8 ∧ 0 < C ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        ∃ J : ℕ,
          let rho : ℝ := R / (3 : ℝ) ^ J
          rho ≤ c * r ∧ c * r < 3 * rho ∧
          0 < rho ∧ rho ≤ r / 8 ∧
          rho ^ (-1 - eta) ≤ C * r ^ (-1 - eta) := by
  let c : ℝ := min R (1 / 8)
  have hc : 0 < c := lt_min hR (by norm_num)
  have hcR : c ≤ R := min_le_left _ _
  have hc8 : c ≤ 1 / 8 := min_le_right _ _
  let C : ℝ := (c / 3) ^ (-1 - eta)
  have hc3 : 0 < c / 3 := by positivity
  have hC : 0 < C := Real.rpow_pos_of_pos hc3 _
  refine ⟨c, C, hc, hcR, hc8, hC, ?_⟩
  intro r hr hr1
  obtain ⟨J, hupper, hlower⟩ :=
    lem_20_collar_family_mesh_scale R c hR hc hcR r hr hr1
  refine ⟨J, hupper, hlower, ?_, ?_, ?_⟩
  · exact div_pos hR (by positivity)
  · have hcr : c * r ≤ (1 / 8 : ℝ) * r :=
      mul_le_mul_of_nonneg_right hc8 hr.le
    calc
      R / (3 : ℝ) ^ J ≤ c * r := hupper
      _ ≤ (1 / 8 : ℝ) * r := hcr
      _ = r / 8 := by ring
  · have hcrho : (c / 3) * r ≤ R / (3 : ℝ) ^ J := by
      have h : 0 ≤ 3 * (R / (3 : ℝ) ^ J) - c * r := by linarith
      nlinarith
    have hpow := Real.rpow_le_rpow_of_nonpos
      (mul_pos hc3 hr) hcrho (by linarith : -1 - eta ≤ 0)
    calc
      (R / (3 : ℝ) ^ J) ^ (-1 - eta)
          ≤ ((c / 3) * r) ^ (-1 - eta) := hpow
      _ = C * r ^ (-1 - eta) := by
        rw [Real.mul_rpow hc3.le hr.le]

/-! ### Real-width collar construction  -/

/-- The distance to the complement of the cube is at most the lower margin
in any coordinate. -/
theorem aux_lem_20_collar_family_infDist_le_lower
    (d : ℕ) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (y : SpatialCoordinates d) (i : Fin d) (hy : z i - R / 2 ≤ y i) :
    Metric.infDist y (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤
      y i - (z i - R / 2) := by
  let w : SpatialCoordinates d := Function.update y i (z i - R / 2)
  have hw : w ∈ (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ := by
    intro hwQ
    rw [centeredCube_eq_pi z hR] at hwQ
    have hwi := hwQ i (Set.mem_univ i)
    have hbad : z i - R / 2 < z i - R / 2 := by
      simpa [w] using hwi.1
    exact lt_irrefl _ hbad
  calc Metric.infDist y (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ
      ≤ dist y w := Metric.infDist_le_dist_of_mem hw
    _ = y i - (z i - R / 2) :=
      aux_lem_20_collar_family_smooth_collar_dist_update_of_le d y (z i - R / 2) i hy

/-- The distance to the complement of the cube is at most the upper margin
in any coordinate. -/
theorem aux_lem_20_collar_family_infDist_le_upper
    (d : ℕ) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (y : SpatialCoordinates d) (i : Fin d) (hy : y i ≤ z i + R / 2) :
    Metric.infDist y (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤
      (z i + R / 2) - y i := by
  let w : SpatialCoordinates d := Function.update y i (z i + R / 2)
  have hw : w ∈ (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ := by
    intro hwQ
    rw [centeredCube_eq_pi z hR] at hwQ
    have hwi := hwQ i (Set.mem_univ i)
    have hbad : z i + R / 2 < z i + R / 2 := by
      simpa [w] using hwi.2
    exact lt_irrefl _ hbad
  calc Metric.infDist y (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ
      ≤ dist y w := Metric.infDist_le_dist_of_mem hw
    _ = (z i + R / 2) - y i :=
      aux_lem_20_collar_family_smooth_collar_dist_update_of_ge d y (z i + R / 2) i hy

/-- Coordinate margins bound the distance to the complement from below. -/
theorem aux_lem_20_collar_family_le_infDist_of_margins
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (y : SpatialCoordinates d) (s : ℝ)
    (h : ∀ i : Fin d, s ≤ y i - (z i - R / 2) ∧ s ≤ (z i + R / 2) - y i) :
    s ≤ Metric.infDist y (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ := by
  have hcomp := aux_lem_20_collar_family_smooth_collar_compl_nonempty d hd z R hR
  rw [Metric.le_infDist hcomp]
  intro w hw
  have hwc : ∃ i : Fin d, w i ≤ z i - R / 2 ∨ z i + R / 2 ≤ w i := by
    by_contra hcon
    push Not at hcon
    apply hw
    rw [centeredCube_eq_pi z hR]
    intro i _
    exact ⟨(hcon i).1, (hcon i).2⟩
  obtain ⟨i, hi | hi⟩ := hwc
  · have h1 := aux_lem_20_collar_family_smooth_collar_coordinate_dist_le d y w i
    rw [Real.dist_eq] at h1
    have h2 := le_abs_self (y i - w i)
    linarith [(h i).1]
  · have h1 := aux_lem_20_collar_family_smooth_collar_coordinate_dist_le d y w i
    rw [Real.dist_eq] at h1
    have h2 := neg_abs_le (y i - w i)
    linarith [(h i).2]

/-- Layer quantization, near side: if one point of an open mesh cell is within
`j` mesh widths of the boundary, then so is every point of that cell. -/
theorem aux_lem_20_collar_family_layer_le
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (Jr : ℕ) (k : OddGridIndex d (triadicHalf Jr)) (j : ℕ) (hj : 1 ≤ j)
    (x : SpatialCoordinates d)
    (hx : x ∈ (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)))
    (hxd : Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤
      (j : ℝ) * (R / (3 : ℝ) ^ Jr)) :
    ∀ y ∈ (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)),
      Metric.infDist y (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤
        (j : ℝ) * (R / (3 : ℝ) ^ Jr) := by
  intro y hy
  have hρ : R / (2 * (triadicHalf Jr : ℝ) + 1) = R / (3 : ℝ) ^ Jr := by
    rw [triadic_denominator]
  have hρpos : 0 < R / (3 : ℝ) ^ Jr := by positivity
  have hRρ : R = (2 * (triadicHalf Jr : ℝ) + 1) * (R / (3 : ℝ) ^ Jr) := by
    rw [← triadic_denominator Jr]
    field_simp
  have hjpos : 0 < (j : ℝ) * (R / (3 : ℝ) ^ Jr) :=
    mul_pos (by exact_mod_cast hj) hρpos
  obtain ⟨i, hi⟩ :=
    aux_lem_20_collar_family_smooth_collar_margin_small d hd z R hR x _ hjpos hxd
  have hxc := (mem_oddGridCell z hR (triadicHalf Jr) k x).mp hx i
  have hyc := (mem_oddGridCell z hR (triadicHalf Jr) k y).mp hy i
  rw [hρ] at hxc hyc
  have hklt : (k i).val < 2 * triadicHalf Jr + 1 := (k i).isLt
  have hkle : ((k i).val : ℝ) ≤ 2 * (triadicHalf Jr : ℝ) := by
    have : (k i).val ≤ 2 * triadicHalf Jr := by omega
    exact_mod_cast this
  have hk0 : (0 : ℝ) ≤ (k i).val := Nat.cast_nonneg _
  generalize R / (3 : ℝ) ^ Jr = ρ at hρpos hRρ hjpos hxc hyc hi ⊢
  have hk0ρ : 0 ≤ ((k i).val : ℝ) * ρ := mul_nonneg hk0 hρpos.le
  have hkleρ : ((k i).val : ℝ) * ρ ≤ 2 * (triadicHalf Jr : ℝ) * ρ :=
    mul_le_mul_of_nonneg_right hkle hρpos.le
  rcases hi with hi | hi
  · have h1 : ((k i).val : ℝ) * ρ < (j : ℝ) * ρ := by linarith
    have h2 : ((k i).val : ℝ) < j := lt_of_mul_lt_mul_right h1 hρpos.le
    have h3 : (k i).val < j := by exact_mod_cast h2
    have h4 : ((k i).val : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h3
    have h5 : (((k i).val : ℝ) + 1) * ρ ≤ (j : ℝ) * ρ :=
      mul_le_mul_of_nonneg_right h4 hρpos.le
    have hyl : z i - R / 2 ≤ y i := by linarith
    have := aux_lem_20_collar_family_infDist_le_lower d z R hR y i hyl
    linarith
  · have h1 : (2 * (triadicHalf Jr : ℝ) - (k i).val) * ρ < (j : ℝ) * ρ := by linarith
    have h2 : 2 * (triadicHalf Jr : ℝ) - (k i).val < j := lt_of_mul_lt_mul_right h1 hρpos.le
    have h2' : ((2 * triadicHalf Jr : ℕ) : ℝ) < ((j + (k i).val : ℕ) : ℝ) := by
      push_cast; linarith
    have h3 : 2 * triadicHalf Jr < j + (k i).val := by exact_mod_cast h2'
    have h4' : 2 * triadicHalf Jr + 1 ≤ j + (k i).val := h3
    have h4 : 2 * (triadicHalf Jr : ℝ) + 1 ≤ (j : ℝ) + (k i).val := by exact_mod_cast h4'
    have h5 : (2 * (triadicHalf Jr : ℝ) + 1 - (k i).val) * ρ ≤ (j : ℝ) * ρ :=
      mul_le_mul_of_nonneg_right (by linarith) hρpos.le
    have hyu : y i ≤ z i + R / 2 := by linarith
    have := aux_lem_20_collar_family_infDist_le_upper d z R hR y i hyu
    linarith

/-- Layer quantization, deep side: if one point of an open mesh cell is at
least `j` mesh widths from the boundary, then so is every point of that cell. -/
theorem aux_lem_20_collar_family_layer_ge
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (Jr : ℕ) (k : OddGridIndex d (triadicHalf Jr)) (j : ℕ)
    (x : SpatialCoordinates d)
    (hx : x ∈ (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)))
    (hxd : (j : ℝ) * (R / (3 : ℝ) ^ Jr) ≤
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ) :
    ∀ y ∈ (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)),
      (j : ℝ) * (R / (3 : ℝ) ^ Jr) ≤
        Metric.infDist y (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ := by
  intro y hy
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    simpa using Metric.infDist_nonneg
  have hρ : R / (2 * (triadicHalf Jr : ℝ) + 1) = R / (3 : ℝ) ^ Jr := by
    rw [triadic_denominator]
  have hρpos : 0 < R / (3 : ℝ) ^ Jr := by positivity
  have hRρ : R = (2 * (triadicHalf Jr : ℝ) + 1) * (R / (3 : ℝ) ^ Jr) := by
    rw [← triadic_denominator Jr]
    field_simp
  have hs : 0 < (j : ℝ) * (R / (3 : ℝ) ^ Jr) :=
    mul_pos (by exact_mod_cast hjpos) hρpos
  have hm := aux_lem_20_collar_family_smooth_collar_margins_ge d z R hR x _ hs hxd
  apply aux_lem_20_collar_family_le_infDist_of_margins d hd z R hR y
  intro i
  have hxc := (mem_oddGridCell z hR (triadicHalf Jr) k x).mp hx i
  have hyc := (mem_oddGridCell z hR (triadicHalf Jr) k y).mp hy i
  rw [hρ] at hxc hyc
  have hmi := hm i
  generalize R / (3 : ℝ) ^ Jr = ρ at hρpos hRρ hs hxc hyc hmi ⊢
  have h1 : (j : ℝ) * ρ < (((k i).val : ℝ) + 1) * ρ := by linarith [hmi.1]
  have h2 : (j : ℝ) < (k i).val + 1 := lt_of_mul_lt_mul_right h1 hρpos.le
  have h2' : (j : ℝ) < (((k i).val + 1 : ℕ) : ℝ) := by push_cast; exact h2
  have h3 : j < (k i).val + 1 := by exact_mod_cast h2'
  have h4 : (j : ℝ) ≤ (k i).val := by exact_mod_cast Nat.lt_succ_iff.mp h3
  have h5 : (j : ℝ) * ρ ≤ ((k i).val : ℝ) * ρ := mul_le_mul_of_nonneg_right h4 hρpos.le
  have g1 : (j : ℝ) * ρ < (2 * (triadicHalf Jr : ℝ) + 1 - (k i).val) * ρ := by
    linarith [hmi.2]
  have g2 : (j : ℝ) < 2 * (triadicHalf Jr : ℝ) + 1 - (k i).val :=
    lt_of_mul_lt_mul_right g1 hρpos.le
  have g2' : (((j + (k i).val) : ℕ) : ℝ) < ((2 * triadicHalf Jr + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  have g3 : j + (k i).val < 2 * triadicHalf Jr + 1 := by exact_mod_cast g2'
  have g4 : (j : ℝ) + (k i).val ≤ 2 * (triadicHalf Jr : ℝ) := by
    have : j + (k i).val ≤ 2 * triadicHalf Jr := by omega
    exact_mod_cast this
  have g5 : (j : ℝ) * ρ ≤ (2 * (triadicHalf Jr : ℝ) - (k i).val) * ρ :=
    mul_le_mul_of_nonneg_right (by linarith) hρpos.le
  constructor <;> linarith

/-- A smooth one-mesh-width band collar: the explicit product profile of
`lem_20_collar_family_smooth_collar`, shifted so that it vanishes within
distance `a` of the boundary, equals one from distance `a + w`, and has
gradient at most `2 d M / w`. -/
theorem aux_lem_20_collar_family_band_profile
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (M : ℝ) (hM : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ M)
    (a w : ℝ) (ha : 0 < a) (hw : 0 < w) :
    ContDiff ℝ ∞ (aux_lem_20_collar_family_smooth_collar_profile d z (R - 2 * a + w) (w / 2)) ∧
      (∀ x, 0 ≤ aux_lem_20_collar_family_smooth_collar_profile d z (R - 2 * a + w) (w / 2) x ∧
        aux_lem_20_collar_family_smooth_collar_profile d z (R - 2 * a + w) (w / 2) x ≤ 1) ∧
      (∀ x, Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ a →
        aux_lem_20_collar_family_smooth_collar_profile d z (R - 2 * a + w) (w / 2) x = 0) ∧
      (∀ x, a + w ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        aux_lem_20_collar_family_smooth_collar_profile d z (R - 2 * a + w) (w / 2) x = 1) ∧
      (∀ x, ‖fderiv ℝ
        (aux_lem_20_collar_family_smooth_collar_profile d z (R - 2 * a + w) (w / 2)) x‖ ≤
          2 * (d : ℝ) * M / w) := by
  have hw2 : 0 < w / 2 := half_pos hw
  have hden : 2 * (w / 2) = w := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold aux_lem_20_collar_family_smooth_collar_profile
    apply contDiff_prod
    intro i _
    exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
      (Real.smoothTransition.contDiff.comp (by fun_prop))
  · intro x
    unfold aux_lem_20_collar_family_smooth_collar_profile
    constructor
    · exact Finset.prod_nonneg (fun i _ => mul_nonneg
        (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))
    · exact Finset.prod_le_one₀ (fun i _ => mul_nonneg
        (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))
        (fun i _ => (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
          (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _))
  · intro x hx
    obtain ⟨i, hi | hi⟩ :=
      aux_lem_20_collar_family_smooth_collar_margin_small d hd z R hR x a ha hx
    · unfold aux_lem_20_collar_family_smooth_collar_profile
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [mul_eq_zero]
      left
      apply Real.smoothTransition.zero_of_nonpos
      rw [hden]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le
    · unfold aux_lem_20_collar_family_smooth_collar_profile
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [mul_eq_zero]
      right
      apply Real.smoothTransition.zero_of_nonpos
      rw [hden]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le
  · intro x hx
    have hs : 0 < a + w := by linarith
    have hm := aux_lem_20_collar_family_smooth_collar_margins_ge d z R hR x (a + w) hs hx
    unfold aux_lem_20_collar_family_smooth_collar_profile
    apply Finset.prod_eq_one
    intro i _
    have hl : 1 ≤ (x i - (z i - (R - 2 * a + w) / 2) - w / 2) / (2 * (w / 2)) := by
      rw [hden, le_div_iff₀ hw]
      linarith [(hm i).1]
    have hu : 1 ≤ ((z i + (R - 2 * a + w) / 2) - x i - w / 2) / (2 * (w / 2)) := by
      rw [hden, le_div_iff₀ hw]
      linarith [(hm i).2]
    rw [Real.smoothTransition.one_of_one_le hl, Real.smoothTransition.one_of_one_le hu,
      mul_one]
  · intro x
    have h := aux_lem_20_collar_family_smooth_collar_profile_fderiv_le d z
      (R - 2 * a + w) (w / 2) hw2 M hM x
    have heq : (d : ℝ) * M / (w / 2) = 2 * (d : ℝ) * M / w := by
      field_simp
    rw [heq] at h
    exact h

/-- On a mesh cell where the datum is the constant `c`, the harmonic
interpolant's Sobolev data are `c` and `0` almost everywhere
(`lem_20_collar_family_cell_constant` for the continuous positive coefficient). -/
theorem aux_lem_20_collar_family_cell_value
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (a : SpatialCoordinates d → ℝ) (ha : Continuous a) (hapos : ∀ x, 0 < a x)
    (Jr : ℕ) (thetaR : SpatialCoordinates d → ℝ)
    (thetaRH1 : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hH1 : thetaRH1.toFun = thetaR)
    (u : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (v : S.space) (hv : v.val = sobolevDataOfH1 u)
    (k : OddGridIndex d (triadicHalf Jr))
    (hharm : IsWeaklyHarmonicOn a
        (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))
        (u.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
          (oddGridCell_subset z hR (triadicHalf Jr) k)))
    (htrace : HasZeroTraceDifferenceOn
        (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))
        (u.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
          (oddGridCell_subset z hR (triadicHalf Jr) k))
        (thetaRH1.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
          (oddGridCell_subset z hR (triadicHalf Jr) k)))
    (c : ℝ)
    (hc : ∀ y ∈ (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)),
      thetaR y = c) :
    ∀ᵐ x ∂(volume.restrict
        (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))),
      (v.val.1 : SpatialCoordinates d → ℝ) x = c ∧
        ∀ i : Fin d, (v.val.2 i : SpatialCoordinates d → ℝ) x = 0 := by
  obtain ⟨lam, Lam, hlam, hbd⟩ := aux_lem_cutoffs_pos_bounds a ha hapos
    (closure (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)))
    (isCompact_closure_centeredCube _ _)
  have hEll : IsEllipticFieldOn lam Lam
      (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))
      (scalarCoeffField a) :=
    isEllipticFieldOn_scalar
      (oddGridCell z R hR (triadicHalf Jr) k).isOpen.measurableSet
      ha.measurable hlam (fun x hx => hbd x (subset_closure hx))
  have hcc := lem_20_collar_family_cell_constant d hd
    (oddGridCell z R hR (triadicHalf Jr) k) (aux_lem_cutoffs_cell_dom z hR _ k)
    (aux_lem_cutoffs_cell_nonempty z hR _ k) a lam Lam hEll
    (thetaRH1.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
      (oddGridCell_subset z hR (triadicHalf Jr) k))
    (u.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
      (oddGridCell_subset z hR (triadicHalf Jr) k)) c
    (fun y hy => by
      change thetaRH1.toFun y = c
      rw [hH1]
      exact hc y hy) hharm htrace
  have hsub := oddGridCell_subset z hR (triadicHalf Jr) k
  have h1 : (v.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))] u.toFun := by
    rw [hv]
    exact ae_restrict_of_ae_restrict_of_subset hsub (sobolevDataOfH1_fst_coeFn u)
  have h2 : ∀ i : Fin d, (v.val.2 i : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))]
        fun x => u.grad x i := by
    intro i
    rw [hv]
    exact ae_restrict_of_ae_restrict_of_subset hsub (sobolevDataOfH1_snd_coeFn u i)
  have h2' := ae_all_iff.mpr h2
  filter_upwards [hcc, h1, h2'] with x hx hx1 hx2
  refine ⟨?_, fun i => ?_⟩
  · rw [hx1]
    exact hx.1
  · rw [hx2 i]
    exact hx.2 i

/-- Almost every point of the cube lies in an open mesh cell. -/
theorem aux_lem_20_collar_family_ae_cover
    (d : ℕ) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (Jr : ℕ) :
    ∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
      x ∈ ⋃ k : OddGridIndex d (triadicHalf Jr),
        (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)) := by
  have h1 := (oddGrid_union_ae_eq z hR (triadicHalf Jr)).mem_iff
  have h2 : ∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
      x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet
  filter_upwards [ae_restrict_of_ae h1, h2] with x hx hxQ
  exact hx.mpr hxQ

/-- The real-width collar clauses from a mesh interpolant whose smooth datum
vanishes up to `j0` mesh widths and equals one from `j0 + 1` mesh widths,
when `r ≤ j0 ρ` and `(j0 + 1) ρ ≤ 3 r`. -/
theorem aux_lem_20_collar_family_band_ae
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (a : SpatialCoordinates d → ℝ) (ha : Continuous a) (hapos : ∀ x, 0 < a x)
    (Jr : ℕ) (thetaR : SpatialCoordinates d → ℝ)
    (thetaRH1 : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hH1 : thetaRH1.toFun = thetaR)
    (u : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (v : S.space) (hv : v.val = sobolevDataOfH1 u)
    (hcell : ∀ k : OddGridIndex d (triadicHalf Jr),
      IsWeaklyHarmonicOn a
          (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))
          (u.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
            (oddGridCell_subset z hR (triadicHalf Jr) k)) ∧
        HasZeroTraceDifferenceOn
          (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))
          (u.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
            (oddGridCell_subset z hR (triadicHalf Jr) k))
          (thetaRH1.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
            (oddGridCell_subset z hR (triadicHalf Jr) k)))
    (j0 : ℕ) (hj0 : 1 ≤ j0) (r : ℝ)
    (hrj : r ≤ (j0 : ℝ) * (R / (3 : ℝ) ^ Jr))
    (hjr : ((j0 : ℝ) + 1) * (R / (3 : ℝ) ^ Jr) ≤ 3 * r)
    (hzero : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤
        (j0 : ℝ) * (R / (3 : ℝ) ^ Jr) → thetaR x = 0)
    (hone : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      ((j0 : ℝ) + 1) * (R / (3 : ℝ) ^ Jr) ≤
        Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
          thetaR x = 1) :
    (∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r →
        (v.val.1 : SpatialCoordinates d → ℝ) x = 0) ∧
    (∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
      3 * r ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (v.val.1 : SpatialCoordinates d → ℝ) x = 1) ∧
    (∀ i : Fin d, ∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
      3 * r < Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (v.val.2 i : SpatialCoordinates d → ℝ) x = 0) := by
  have hcover := aux_lem_20_collar_family_ae_cover d z R hR Jr
  have hZ : ∀ k : OddGridIndex d (triadicHalf Jr),
      ∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
        x ∈ (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)) →
        Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r →
          (v.val.1 : SpatialCoordinates d → ℝ) x = 0 := by
    intro k
    by_cases hex : ∃ y ∈ (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)),
        Metric.infDist y (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r
    · obtain ⟨y, hyk, hyd⟩ := hex
      have hall := aux_lem_20_collar_family_layer_le d hd z R hR Jr k j0 hj0 y hyk
        (hyd.trans hrj)
      have hc : ∀ y' ∈ (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)),
          thetaR y' = 0 := fun y' hy' =>
        hzero y' (oddGridCell_subset z hR (triadicHalf Jr) k hy') (hall y' hy')
      have hval := aux_lem_20_collar_family_cell_value d hd z R hR S a ha hapos Jr thetaR
        thetaRH1 hH1 u v hv k (hcell k).1 (hcell k).2 0 hc
      have hval' := (ae_restrict_iff'
        (oddGridCell z R hR (triadicHalf Jr) k).isOpen.measurableSet).mp hval
      filter_upwards [ae_restrict_of_ae hval'] with x hx hxk _
      exact (hx hxk).1
    · push Not at hex
      filter_upwards with x hxk hxd
      exact absurd hxd (not_le.mpr (hex x hxk))
  have hO : ∀ k : OddGridIndex d (triadicHalf Jr),
      ∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
        x ∈ (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)) →
        3 * r ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
          (v.val.1 : SpatialCoordinates d → ℝ) x = 1 ∧
            ∀ i : Fin d, (v.val.2 i : SpatialCoordinates d → ℝ) x = 0 := by
    intro k
    by_cases hex : ∃ y ∈ (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)),
        3 * r ≤ Metric.infDist y (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ
    · obtain ⟨y, hyk, hyd⟩ := hex
      have hyd' : ((j0 + 1 : ℕ) : ℝ) * (R / (3 : ℝ) ^ Jr) ≤
          Metric.infDist y (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ := by
        push_cast
        exact hjr.trans hyd
      have hall := aux_lem_20_collar_family_layer_ge d hd z R hR Jr k (j0 + 1) y hyk hyd'
      have hc : ∀ y' ∈ (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)),
          thetaR y' = 1 := by
        intro y' hy'
        have h := hall y' hy'
        push_cast at h
        exact hone y' (oddGridCell_subset z hR (triadicHalf Jr) k hy') h
      have hval := aux_lem_20_collar_family_cell_value d hd z R hR S a ha hapos Jr thetaR
        thetaRH1 hH1 u v hv k (hcell k).1 (hcell k).2 1 hc
      have hval' := (ae_restrict_iff'
        (oddGridCell z R hR (triadicHalf Jr) k).isOpen.measurableSet).mp hval
      filter_upwards [ae_restrict_of_ae hval'] with x hx hxk _
      exact hx hxk
    · push Not at hex
      filter_upwards with x hxk hxd
      exact absurd hxd (not_le.mpr (hex x hxk))
  have hZall := ae_all_iff.mpr hZ
  have hOall := ae_all_iff.mpr hO
  refine ⟨?_, ?_, fun i => ?_⟩
  · filter_upwards [hZall, hcover] with x hx hxcov hxd
    obtain ⟨k, hxk⟩ := mem_iUnion.mp hxcov
    exact hx k hxk hxd
  · filter_upwards [hOall, hcover] with x hx hxcov hxd
    obtain ⟨k, hxk⟩ := mem_iUnion.mp hxcov
    exact (hx k hxk hxd).1
  · filter_upwards [hOall, hcover] with x hx hxcov hxd
    obtain ⟨k, hxk⟩ := mem_iUnion.mp hxcov
    exact (hx k hxk hxd.le).2 i

/-- The five collar-family clauses for one Sobolev datum `c` at width `r`. -/
def aux_lem_20_collar_family_width_prop (d : ℕ) (z : SpatialCoordinates d) (R : ℝ)
    (hR : 0 < R) (S : ResponseSpace (centeredCube z R hR))
    (aP : PositiveCoefficient (centeredCube z R hR)) (Cbound r : ℝ) (c : S.space) : Prop :=
  (∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
      0 ≤ (c.val.1 : SpatialCoordinates d → ℝ) x ∧
        (c.val.1 : SpatialCoordinates d → ℝ) x ≤ 1) ∧
    (∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r →
        (c.val.1 : SpatialCoordinates d → ℝ) x = 0) ∧
    (∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
      3 * r ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (c.val.1 : SpatialCoordinates d → ℝ) x = 1) ∧
    (∀ i : Fin d, ∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
      3 * r < Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (c.val.2 i : SpatialCoordinates d → ℝ) x = 0) ∧
    responseForm S aP c c ≤ Cbound

/-- Every point of the cube is within half a side of its complement. -/
theorem aux_lem_20_collar_family_infDist_le_half
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (x : SpatialCoordinates d)
    (hx : x ∈ (centeredCube z R hR : Set (SpatialCoordinates d))) :
    Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ R / 2 := by
  let i : Fin d := ⟨0, by omega⟩
  have hx' := hx
  rw [centeredCube_eq_pi z hR] at hx'
  have hxi := hx' i (Set.mem_univ i)
  have h1 := aux_lem_20_collar_family_infDist_le_lower d z R hR x i hxi.1.le
  have h2 := aux_lem_20_collar_family_infDist_le_upper d z R hR x i hxi.2.le
  linarith

/-- For a width at least half the root side the zero datum satisfies every
clause: the one-region and the transition region are empty. -/
theorem aux_lem_20_collar_family_zero_prop
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (aP : PositiveCoefficient (centeredCube z R hR)) (Cbound r : ℝ)
    (hr : 0 < r) (hRr : R ≤ 2 * r) (hC : 0 ≤ Cbound) :
    aux_lem_20_collar_family_width_prop d z R hR S aP Cbound r 0 := by
  have h0 : (((0 : S.space).val.1 : DomainL2 (centeredCube z R hR)) :
      SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))] 0 :=
    Lp.coeFn_zero _ _ _
  have hQ : ∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
      x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet
  have hfar : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ < 3 * r := by
    intro x hx
    have := aux_lem_20_collar_family_infDist_le_half d hd z R hR x hx
    linarith
  refine ⟨?_, ?_, ?_, fun i => ?_, ?_⟩
  · filter_upwards [h0] with x hx
    rw [hx]
    exact ⟨le_refl 0, zero_le_one⟩
  · filter_upwards [h0] with x hx _
    rw [hx]
    rfl
  · filter_upwards [hQ] with x hxQ hxd
    exact absurd hxd (not_le.mpr (hfar x hxQ))
  · filter_upwards [hQ] with x hxQ hxd
    exact absurd hxd (not_lt.mpr (hfar x hxQ).le)
  · simpa using hC

/-- Comparison of the mesh-width energy scale with the requested width. -/
theorem aux_lem_20_collar_family_scale_compare
    (eta C K r ρ : ℝ) (heta : 0 < eta) (hC : 0 ≤ C) (hK : 0 ≤ K) (hr : 0 < r)
    (hrρ : r ≤ 2 * ρ) :
    C * K * ρ ^ (-1 - eta) ≤ C * (2 : ℝ) ^ (1 + eta) * K * r ^ (-1 - eta) := by
  have hr2 : 0 < r / 2 := half_pos hr
  have hle : r / 2 ≤ ρ := by linarith
  have hexp : -1 - eta ≤ 0 := by linarith
  have h1 : ρ ^ (-1 - eta) ≤ (r / 2) ^ (-1 - eta) := Real.rpow_le_rpow_of_nonpos hr2 hle hexp
  have h2 : (r / 2) ^ (-1 - eta) = (2 : ℝ) ^ (1 + eta) * r ^ (-1 - eta) := by
    rw [Real.div_rpow hr.le zero_le_two, show (-1 - eta) = -(1 + eta) by ring,
      Real.rpow_neg zero_le_two, div_inv_eq_mul, mul_comm]
  rw [h2] at h1
  have hCK : 0 ≤ C * K := mul_nonneg hC hK
  calc C * K * ρ ^ (-1 - eta) ≤ C * K * ((2 : ℝ) ^ (1 + eta) * r ^ (-1 - eta)) :=
        mul_le_mul_of_nonneg_left h1 hCK
    _ = C * (2 : ℝ) ^ (1 + eta) * K * r ^ (-1 - eta) := by ring

/-- The collar clause of `lem_cutoffs` (after the common event and majorant
are fixed), rooted at an abstract cube. -/
def aux_lem_20_collar_family_collar_clause (d : ℕ) (z : SpatialCoordinates d) (R : ℝ)
    (hR : 0 < R) (S : ResponseSpace (centeredCube z R hR))
    (a : ℕ → SpatialCoordinates d → ℝ) (aP : ℕ → PositiveCoefficient (centeredCube z R hR))
    (K : ℕ → ℝ) (eta Cgrad Ccollar : ℝ) : Prop :=
  ∀ Jr : ℕ,
    let rho := R / (3 : ℝ) ^ Jr
      ∀ thetaR : SpatialCoordinates d → ℝ,
        ContDiff ℝ ∞ thetaR →
        (∀ x : SpatialCoordinates d,
          0 ≤ thetaR x ∧ thetaR x ≤ 1) →
        (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
          Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) ≤
            rho → thetaR x = 0) →
        (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
          3 * rho ≤ Metric.infDist x
            (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
            thetaR x = 1) →
        (∀ x : SpatialCoordinates d,
          norm (fderiv ℝ thetaR x) ≤ Cgrad / rho) →
        ∀ thetaRH1 : Homogenization.H1Function
          (centeredCube z R hR : Set (SpatialCoordinates d)),
          thetaRH1.toFun = thetaR →
          ∃ collarH : ℕ → Homogenization.H1Function
              (centeredCube z R hR : Set (SpatialCoordinates d)),
            ∃ collarS : ℕ → S.space,
              ∃ collarC : ℕ → SpatialCoordinates d → ℝ,
                ∀ n : ℕ,
                  (collarS n).val = sobolevDataOfH1 (collarH n) ∧
                  ContinuousOn (collarC n)
                    (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
                  (collarS n).val.1 =ᵐ[
                    volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
                    collarC n ∧
                  (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
                    0 ≤ collarC n x ∧ collarC n x ≤ 1) ∧
                  (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
                    Metric.infDist x
                        (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) ≤ rho →
                      collarC n x = 0) ∧
                  (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
                    3 * rho ≤ Metric.infDist x
                        (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
                      collarC n x = 1) ∧
                  (∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                    (centeredCube z R hR : Set (SpatialCoordinates d)),
                    3 * rho < Metric.infDist x
                        (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
                      (collarS n).val.2 i x = 0) ∧
                  (∀ k : OddGridIndex d (triadicHalf Jr),
                    IsWeaklyHarmonicOn (a n)
                      (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))
                      ((collarH n).restrict
                        (oddGridCell z R hR (triadicHalf Jr) k).isOpen
                        (oddGridCell_subset z hR (triadicHalf Jr) k)) ∧
                    HasZeroTraceDifferenceOn
                      (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))
                      ((collarH n).restrict
                        (oddGridCell z R hR (triadicHalf Jr) k).isOpen
                        (oddGridCell_subset z hR (triadicHalf Jr) k))
                      (thetaRH1.restrict
                        (oddGridCell z R hR (triadicHalf Jr) k).isOpen
                        (oddGridCell_subset z hR (triadicHalf Jr) k))) ∧
                  responseForm S (aP n) (collarS n) (collarS n) ≤
                    Ccollar * K n * rho ^ (-1 - eta)

/-- A real width served by the triadic mesh `ρ = R / 3^Jr`: with the band datum
vanishing up to `j0 ρ` and equal to one from `(j0 + 1) ρ`, where `1 ≤ j0 ≤ 2`,
`r ≤ j0 ρ` and `(j0 + 1) ρ ≤ 3 r`, the collar clause of `lem_cutoffs` yields
the full real-width family at `r`. -/
theorem aux_lem_20_collar_family_band_family
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (a : ℕ → SpatialCoordinates d → ℝ) (ha : ∀ n, Continuous (a n))
    (hapos : ∀ n x, 0 < a n x)
    (aP : ℕ → PositiveCoefficient (centeredCube z R hR))
    (K : ℕ → ℝ) (hK : ∀ n, 1 ≤ K n) (eta : ℝ) (heta : 0 < eta)
    (Mt : ℝ) (hMt : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ Mt)
    (Ccollar : ℝ) (hCcollar : 0 < Ccollar)
    (hcol : aux_lem_20_collar_family_collar_clause d z R hR S a aP K eta
      (2 * (d : ℝ) * Mt) Ccollar)
    (Jr j0 : ℕ) (hj0 : 1 ≤ j0) (hj02 : j0 ≤ 2) (r : ℝ) (hr : 0 < r)
    (hrj : r ≤ (j0 : ℝ) * (R / (3 : ℝ) ^ Jr))
    (hjr : ((j0 : ℝ) + 1) * (R / (3 : ℝ) ^ Jr) ≤ 3 * r) :
    ∃ c : ℕ → S.space, ∀ n : ℕ,
      aux_lem_20_collar_family_width_prop d z R hR S (aP n)
        (Ccollar * (2 : ℝ) ^ (1 + eta) * K n * r ^ (-1 - eta)) r (c n) := by
  have hρ : 0 < R / (3 : ℝ) ^ Jr := by positivity
  have hj0r : (1 : ℝ) ≤ j0 := by exact_mod_cast hj0
  have hj02r : (j0 : ℝ) ≤ 2 := by exact_mod_cast hj02
  have ha0 : 0 < (j0 : ℝ) * (R / (3 : ℝ) ^ Jr) := mul_pos (by linarith) hρ
  obtain ⟨hsm, hrange, hz, h1, hgrad⟩ := aux_lem_20_collar_family_band_profile d hd z R hR
    Mt hMt ((j0 : ℝ) * (R / (3 : ℝ) ^ Jr)) (R / (3 : ℝ) ^ Jr) ha0 hρ
  have hzeroF : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) ≤
        R / (3 : ℝ) ^ Jr →
      aux_lem_20_collar_family_smooth_collar_profile d z
        (R - 2 * ((j0 : ℝ) * (R / (3 : ℝ) ^ Jr)) + R / (3 : ℝ) ^ Jr)
        (R / (3 : ℝ) ^ Jr / 2) x = 0 := by
    intro x hx hxd
    rw [aux_lem_20_collar_family_smooth_collar_infDist_frontier_eq d hd z R hR x hx] at hxd
    refine hz x (hxd.trans ?_)
    have := mul_le_mul_of_nonneg_right hj0r hρ.le
    linarith
  have honeF : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      3 * (R / (3 : ℝ) ^ Jr) ≤
        Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
      aux_lem_20_collar_family_smooth_collar_profile d z
        (R - 2 * ((j0 : ℝ) * (R / (3 : ℝ) ^ Jr)) + R / (3 : ℝ) ^ Jr)
        (R / (3 : ℝ) ^ Jr / 2) x = 1 := by
    intro x hx hxd
    rw [aux_lem_20_collar_family_smooth_collar_infDist_frontier_eq d hd z R hR x hx] at hxd
    refine h1 x (le_trans ?_ hxd)
    have := mul_le_mul_of_nonneg_right hj02r hρ.le
    linarith
  have hgeom : IsOpenBoundedConvexDomain
      (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    isOpenBoundedConvexDomain_centeredCube z hR
  let thetaRH1 : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain hgeom (hsm.of_le (by simp))
  have hH1 : thetaRH1.toFun = aux_lem_20_collar_family_smooth_collar_profile d z
      (R - 2 * ((j0 : ℝ) * (R / (3 : ℝ) ^ Jr)) + R / (3 : ℝ) ^ Jr)
      (R / (3 : ℝ) ^ Jr / 2) := rfl
  have hcolJ := hcol Jr _ hsm hrange hzeroF honeF hgrad thetaRH1 hH1
  obtain ⟨collarH, collarS, collarC, hcolN⟩ := hcolJ
  refine ⟨collarS, fun n => ?_⟩
  obtain ⟨hv, _, hae, hrng, _, _, _, hcell, hE⟩ := hcolN n
  have hband := aux_lem_20_collar_family_band_ae d hd z R hR S (a n) (ha n) (hapos n) Jr _
    thetaRH1 hH1 (collarH n) (collarS n) hv hcell j0 hj0 r hrj hjr
    (fun x _ hx => hz x hx)
    (fun x _ hx => h1 x (by linarith))
  obtain ⟨hZ, hO, hG⟩ := hband
  refine ⟨?_, hZ, hO, hG, ?_⟩
  · filter_upwards [hae, ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet]
      with x hx hxQ
    rw [hx]
    exact hrng x (subset_closure hxQ)
  · refine hE.trans ?_
    have hr2 : r ≤ 2 * (R / (3 : ℝ) ^ Jr) := by
      have := mul_le_mul_of_nonneg_right hj02r hρ.le
      linarith
    exact aux_lem_20_collar_family_scale_compare eta Ccollar (K n) r _ heta hCcollar.le
      (zero_le_one.trans (hK n)) hr hr2

/-- The collar family at one real width `r > 0` (the clauses force nothing new
for `r ≥ R/2`, where the zero datum is used). -/
theorem aux_lem_20_collar_family_width
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (a : ℕ → SpatialCoordinates d → ℝ) (ha : ∀ n, Continuous (a n))
    (hapos : ∀ n x, 0 < a n x)
    (aP : ℕ → PositiveCoefficient (centeredCube z R hR))
    (K : ℕ → ℝ) (hK : ∀ n, 1 ≤ K n) (eta : ℝ) (heta : 0 < eta)
    (Mt : ℝ) (hMt : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ Mt)
    (Ccollar : ℝ) (hCcollar : 0 < Ccollar)
    (hcol : aux_lem_20_collar_family_collar_clause d z R hR S a aP K eta
      (2 * (d : ℝ) * Mt) Ccollar)
    (r : ℝ) (hr : 0 < r) :
    ∃ c : ℕ → S.space, ∀ n : ℕ,
      aux_lem_20_collar_family_width_prop d z R hR S (aP n)
        (Ccollar * (2 : ℝ) ^ (1 + eta) * K n * r ^ (-1 - eta)) r (c n) := by
  by_cases hRr : R ≤ 2 * r
  · refine ⟨fun _ => 0, fun n => aux_lem_20_collar_family_zero_prop d hd z R hR S (aP n) _ r
      hr hRr ?_⟩
    exact mul_nonneg (mul_nonneg (mul_nonneg hCcollar.le (Real.rpow_nonneg zero_le_two _))
      (zero_le_one.trans (hK n))) (Real.rpow_nonneg hr.le _)
  · push Not at hRr
    have hr' : 0 < 3 * r / (2 * R) := by positivity
    have hr'1 : 3 * r / (2 * R) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    obtain ⟨Jr, hJ1, hJ2⟩ :=
      lem_20_collar_family_mesh_scale R R hR hR le_rfl (3 * r / (2 * R)) hr' hr'1
    have hRc : R * (3 * r / (2 * R)) = 3 * r / 2 := by
      field_simp
    rw [hRc] at hJ1 hJ2
    by_cases hrρ : r ≤ R / (3 : ℝ) ^ Jr
    · exact aux_lem_20_collar_family_band_family d hd z R hR S a ha hapos aP K hK eta heta
        Mt hMt Ccollar hCcollar hcol Jr 1 le_rfl (by norm_num) r hr
        (by push_cast; linarith) (by push_cast; linarith)
    · push Not at hrρ
      exact aux_lem_20_collar_family_band_family d hd z R hR S a ha hapos aP K hK eta heta
        Mt hMt Ccollar hCcollar hcol Jr 2 (by norm_num) le_rfl r hr
        (by push_cast; linarith) (by push_cast; linarith)

/-- The collar family for every real width, with the collar clause of
`lem_cutoffs` at the root cube as input. -/
theorem aux_lem_20_collar_family_rooted
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (a : ℕ → SpatialCoordinates d → ℝ) (ha : ∀ n, Continuous (a n))
    (hapos : ∀ n x, 0 < a n x)
    (aP : ℕ → PositiveCoefficient (centeredCube z R hR))
    (K : ℕ → ℝ) (hK : ∀ n, 1 ≤ K n) (eta : ℝ) (heta : 0 < eta)
    (Mt : ℝ) (hMt : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ Mt)
    (Ccollar : ℝ) (hCcollar : 0 < Ccollar)
    (hcol : aux_lem_20_collar_family_collar_clause d z R hR S a aP K eta
      (2 * (d : ℝ) * Mt) Ccollar) :
    ∃ chi : ℝ → ℕ → S.space, ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ n : ℕ,
      aux_lem_20_collar_family_width_prop d z R hR S (aP n)
        (Ccollar * (2 : ℝ) ^ (1 + eta) * K n * r ^ (-1 - eta)) r (chi r n) := by
  have hex : ∀ r : ℝ, ∃ c : ℕ → S.space, 0 < r → r ≤ 1 → ∀ n : ℕ,
      aux_lem_20_collar_family_width_prop d z R hR S (aP n)
        (Ccollar * (2 : ℝ) ^ (1 + eta) * K n * r ^ (-1 - eta)) r (c n) := by
    intro r
    by_cases hr : 0 < r ∧ r ≤ 1
    · obtain ⟨c, hc⟩ := aux_lem_20_collar_family_width d hd z R hR S a ha hapos aP K hK eta
        heta Mt hMt Ccollar hCcollar hcol r hr.1
      exact ⟨c, fun _ _ => hc⟩
    · exact ⟨fun _ => 0, fun h1 h2 => absurd ⟨h1, h2⟩ hr⟩
  choose chi hchi using hex
  exact ⟨chi, hchi⟩

/-- The collar family used at paper label `eq:mfd-2`, constructed below.

Carried-input and supplier checklist:
- SOURCE/TYPING: the fixed root, d >= 2, exponent inequalities, finite
  moment bank and positive extension constant precede delta0 and Ccut.
- conv_represented_estimates  supplies the actual coefficients,
  native killed spaces, source/trace catalogue, cell bounds and grid estimates;
  its complete predicate is retained, including the ultraviolet restriction.
- conv_represented_sequence  supplies the common represented
  event and objectwise bounded constants, never a bound on the original sequence.
- in_J supplies the concrete coefficient functionals in those bounds.
- lem_cutoffs  supplies the collar construction and energy
  calculation on mesh widths. mesh_interpolator supplies the harmonic mesh;
  lem_extension supplies eq:mfd-2 and eq:mfd-3;
  cell_boundary_continuity supplies boundary continuity.
- CONCLUDED: a single chi : Real -> Nat -> S0.space for every real
  0 < r <= 1, all five geometric/energy clauses of lem_20, one positive Ccut
  independent of r,n, and measurable KN with the prescribed moments and
  represented-sequence boundedness. There is no cutoff-family hypothesis.
- The common event is chosen before the width. Deterministic mesh choice,
  smooth collar data, harmonic gluing, a.e. gradient support, and the uniform
  energy summation are construction obligations, not carried assumptions.
- The four arbitrary-width construction steps are exposed by
  `lem_20_collar_family_mesh_scale`, `lem_20_collar_family_smooth_collar`,
  `lem_20_collar_family_cell_constant`, and
  `lem_20_collar_family_response_congr`; they are conclusions of fine children,
  not carried hypotheses.

 records this missing construction target.
The existing triadic theorem is NOT asserted to have a full-width conclusion.
 remains the separate recorded ultraviolet
source question; no stronger grid estimate or eventual-index guard is added.
The proof below constructs the family under the displayed hypotheses;
it does not change the source range qualification above.
-/
theorem lem_20_collar_family
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (beta alpha eta t : ℝ)
    (hbeta : 1 / 2 < beta) (hbetaalpha : beta < alpha)
    (halpha : alpha < 1) (heta : 0 < eta)
    (htlow : (d : ℝ) - 1 < t) (htupper : t < (d : ℝ))
    (hetaalpha : 1 + eta < 2 * alpha)
    (orders : Finset ℝ) (horders : ∀ p ∈ orders, 0 < p)
    (Cext : ℝ) (hCext : 0 < Cext) :
    ∃ delta0 Ccut : ℝ, 0 < delta0 ∧ 0 < Ccut ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        M.delta ≤ delta0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P]
        (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
        (J : Type) [Countable J] [DecidableEq J] (j0 : J)
        (z : J → SpatialCoordinates d) (rad : J → ℝ)
        (hrad : ∀ j, 0 < rad j)
        (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
        (D : ∀ j, Submodule ℚ
          (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
        [_hDc : ∀ j, Countable (D j)]
        (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
        (T : J → Type) [_hTc : ∀ j, Countable (T j)]
        (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
        (thetaH1 : ∀ j, T j →
          Homogenization.H1Function
            (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
        (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
        (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
        (ucell : ∀ j, T j → ℕ → Ω →
          Homogenization.H1Function
            (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
        (E : _root_.SubdiffusiveProcess.Paper.in_J d)
        (Index : Type) [Countable Index]
        (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
        (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
        (coercivityKey extensionKey lambdaKey : J → Index)
        (sourceResponseKey sourceGrowthKey sourceHolderKey :
          ∀ j, (D j) → Index)
        (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
        (Grid : Type) [Countable Grid]
        (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
        (gridKey : Grid → Index)
        (_hz0 : z j0 = z0) (_hrad0 : rad j0 = R)
        (_hrepresented :
          _root_.SubdiffusiveProcess.Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
            S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
            Index resp respLim constants G coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
            cellGrowthKey cellHolderKey Grid origin gridRoot gridKey),
        let Q := centeredCube (z j0) (rad j0) (hrad j0)
        let S0 := S j0
        let aN := fun (omega : Ω) (n : ℕ) =>
          _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n)
            (z j0) (hrad j0)
        ∃ KN : ℕ → Ω → ℝ, ∃ Ggood : Set Ω,
          MeasurableSet Ggood ∧ Ggood ⊆ G ∧ P (Ggoodᶜ) = 0 ∧
          (∀ n : ℕ, Measurable (KN n)) ∧
          (∀ n : ℕ, ∀ omega : Ω, 1 ≤ KN n omega) ∧
          (∀ p ∈ orders, ∃ Cp : ℝ, 0 ≤ Cp ∧
            ∀ n : ℕ,
              MemLp (KN n) (ENNReal.ofReal p) P ∧
                eLpNorm (KN n) (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cp) ∧
          (∀ omega ∈ Ggood,
            BddAbove (Set.range (fun n : ℕ => KN n omega))) ∧
          ∀ omega ∈ Ggood,
            ∃ chi : ℝ → ℕ → S0.space,
              (∀ (r : ℝ), 0 < r → r ≤ 1 → ∀ n : ℕ,
                (∀ᵐ x ∂(volume.restrict
                  (Q : Set (SpatialCoordinates d))),
                  0 ≤ ((chi r n).val.1 : SpatialCoordinates d → ℝ) x ∧
                    ((chi r n).val.1 : SpatialCoordinates d → ℝ) x ≤ 1) ∧
                (∀ᵐ x ∂(volume.restrict
                  (Q : Set (SpatialCoordinates d))),
                  Metric.infDist x
                      (Q : Set (SpatialCoordinates d))ᶜ ≤ r →
                    ((chi r n).val.1 : SpatialCoordinates d → ℝ) x = 0) ∧
                (∀ᵐ x ∂(volume.restrict
                  (Q : Set (SpatialCoordinates d))),
                  3 * r ≤ Metric.infDist x
                      (Q : Set (SpatialCoordinates d))ᶜ →
                    ((chi r n).val.1 : SpatialCoordinates d → ℝ) x = 1) ∧
                (∀ i : Fin d, ∀ᵐ x ∂(volume.restrict
                  (Q : Set (SpatialCoordinates d))),
                  3 * r < Metric.infDist x
                      (Q : Set (SpatialCoordinates d))ᶜ →
                    ((chi r n).val.2 i : SpatialCoordinates d → ℝ) x = 0) ∧
                responseForm S0 (aN omega n) (chi r n) (chi r n) ≤
                  Ccut * KN n omega * r ^ (-1 - eta)) := by
  obtain ⟨Mt, hMtpos, hMt⟩ := aux_lem_20_collar_family_smooth_collar_deriv_transition_bound
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hCgrad : 0 < 2 * (d : ℝ) * Mt := mul_pos (mul_pos two_pos hd0) hMtpos
  have hLC := lem_cutoffs d hd z0 R hR beta alpha eta t hbeta hbetaalpha halpha heta htlow
    htupper hetaalpha orders horders Cext (2 * (d : ℝ) * Mt) hCext hCgrad
  obtain ⟨delta0, Ccollar, hdelta0, hCcollar, hLC'⟩ := hLC
  refine ⟨delta0, Ccollar * (2 : ℝ) ^ (1 + eta), hdelta0,
    mul_pos hCcollar (Real.rpow_pos_of_pos two_pos _), ?_⟩
  intro M H hM Ω _ P _ cutoff env J _ _ j0 z rad hrad S D _ f T _ theta thetaH1 usrc srcRep
    ucell E Index _ resp respLim constants G coercivityKey extensionKey lambdaKey
    sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey Grid _ origin gridRoot gridKey hz0 hrad0 hrepresented Q S0 aN
  have hL := hLC' M H hM Ω P cutoff env J j0 z rad hrad S D f T theta thetaH1 usrc srcRep
    ucell E Index resp respLim constants G coercivityKey extensionKey lambdaKey
    sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey Grid origin gridRoot gridKey hz0 hrad0 hrepresented
  obtain ⟨KN, Ggood, hGm, hGG, hGP, hKNm, hKN1, hKNmom, hKNbdd, hmain⟩ := hL
  refine ⟨KN, Ggood, hGm, hGG, hGP, hKNm, hKN1, hKNmom, hKNbdd, fun omega homega => ?_⟩
  exact aux_lem_20_collar_family_rooted d hd (z j0) (rad j0) (hrad j0) (S j0)
    (fun n => cutoffCoefficient M H (env n omega) (cutoff n))
    (fun n => (aux_lem_cutoffs_cutoffCoefficient_cont_pos M H (env n omega) (cutoff n)).1)
    (fun n => (aux_lem_cutoffs_cutoffCoefficient_cont_pos M H (env n omega) (cutoff n)).2)
    (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j0) (hrad j0))
    (fun n => KN n omega) (fun n => hKN1 n omega) eta heta Mt hMt Ccollar hCcollar
    (hmain omega homega).2

end SubdiffusiveProcess.Paper
