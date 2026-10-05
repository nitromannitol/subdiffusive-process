module

public import SubdiffusiveProcess.Paper.calib_weighted_form_data
public import SubdiffusiveProcess.Paper.calib_weighted_green_limit
public import SubdiffusiveProcess.Paper.calib_boundary_glb
public import SubdiffusiveProcess.Paper.calibResp
public import SubdiffusiveProcess.Paper.calib_h0_large_cell_bounds

@[expose] public section

/-! **One side of the boundary identification.**  For one cube family and one represented sequence: the
infrared-free responses `Λ⁰_{N_n,Q_{3^m}}(e₀)(β_n)` that converge to `L` are the infimum over continuous
extensions of `e₀·x` of the energy measure `Γ_{E⁰}` of the weighted form `E⁰ = ∫ exp g dΓ_E` of the limit form
`E` of the infrared-carrying sequence, on the inner cube.  Deterministic. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Scalar ratio bounds. -/
theorem aux_calib_side_boundary_ratio_bounds (c0 δ D : ℝ) (hc0 : 0 < c0) (hδ : |δ| ≤ D) :
    Real.exp (-D) * (c0 * Real.exp δ) ≤ c0 ∧ c0 ≤ Real.exp D * (c0 * Real.exp δ) := by
  have h1 := (abs_le.1 hδ)
  constructor
  · calc Real.exp (-D) * (c0 * Real.exp δ) = c0 * Real.exp (-D + δ) := by
          rw [Real.exp_add]; ring
      _ ≤ c0 * 1 := mul_le_mul_of_nonneg_left
          (by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith)) hc0.le
      _ = c0 := mul_one _
  · calc c0 = c0 * 1 := (mul_one _).symm
      _ ≤ c0 * Real.exp (D + δ) := mul_le_mul_of_nonneg_left
          (by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith)) hc0.le
      _ = Real.exp D * (c0 * Real.exp δ) := by rw [Real.exp_add]; ring

/-- Shifting the infrared potential by a fixed continuous function multiplies the coefficient by its exponential. -/
theorem aux_calib_side_boundary_coeff_shift {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (c : C(SpatialCoordinates d, ℝ))
    (β : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    cutoffCoefficient M (fun β' => H β' + c) β N x =
      cutoffCoefficient M H β N x * Real.exp (c x) := by
  unfold cutoffCoefficient cutoffPotential
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  simp only [ContinuousMap.add_apply]
  ring

/-- **One side of the boundary identification.** -/
theorem calib_side_boundary
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (β : ℕ → BilateralField d) (N : ℕ → ℕ)
    (hinf : C(SpatialCoordinates d, ℝ)) (hh : Tendsto (fun n => H (β n)) atTop (𝓝 hinf))
    (m : ℕ) (zQ : SpatialCoordinates d) (RQ : ℝ) (hRQ : 0 < RQ) (hzQ : zQ = 0)
    (hRQm : RQ = 3 * (3 : ℝ) ^ m)
    (S : ResponseSpace (centeredCube zQ RQ hRQ))
    (hS : S.space = killedSobolevGraph (centeredCube zQ RQ hRQ))
    (G : DomainL2 (centeredCube zQ RQ hRQ) →L[ℝ] DomainL2 (centeredCube zQ RQ hRQ))
    (hG : Tendsto (fun n => volumeResponseOperator S
      (cutoffPositiveCoefficient M H (β n) (N n) zQ hRQ)) atTop (𝓝 G))
    (Bnds : in_represented_bounds_seq d hd zQ RQ hRQ S
      (fun n => cutoffPositiveCoefficient M H (β n) (N n) zQ hRQ) G)
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d)) C)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (hloc : _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal E.toClosedForm)
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (hcell : calib_h0_large_cell_bounds zQ RQ hRQ
      (fun n => cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n))
      t alpha)
    (L : ℝ) (hL : Tendsto (fun n => calibResp d hd M m (N n) (β n)) atTop (𝓝 L)) :
    ∃ (E0 : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))))
      (Gamma0 : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E0.toClosedForm),
      _root_.SubdiffusiveProcess.DirichletForm.IsWeightedForm E.toClosedForm E0.toClosedForm Gamma
        (fun x => Real.exp (aux_calib_weighted_form_data_G hinf
          (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d)) x)) ∧
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E0.toClosedForm
        (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d)) C) ∧
      L = sInf {e : ℝ | ∃ U : DomainL2 (centeredCube zQ RQ hRQ),
        U ∈ E0.toClosedForm.domain ∧ ∃ Uc : SpatialCoordinates d → ℝ,
          ContinuousOn Uc (closure (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))) ∧
          ((U : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))] Uc) ∧
          (∀ x ∈ frontier (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m)
              (pow_pos (zero_lt_three : (0 : ℝ) < 3) m) : Set (SpatialCoordinates d)),
            Uc x = ∑ j : Fin d, aux_thm_c1_envcal_e0 d (by omega) j * x j) ∧
          e = ((Gamma0.measure U) (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m)
            (pow_pos (zero_lt_three : (0 : ℝ) < 3) m) : Set (SpatialCoordinates d))).toReal} := by
  subst hzQ
  subst hRQm
  have : NeZero d := ⟨by omega⟩
  have hr : (0 : ℝ) < (3 : ℝ) ^ m := pow_pos (by norm_num) m
  -- notation
  let Qh : Opens (SpatialCoordinates d) := centeredCube (0 : SpatialCoordinates d) (3 * (3 : ℝ) ^ m) hRQ
  let aC : ℕ → PositiveCoefficient Qh := fun n => cutoffPositiveCoefficient M H (β n) (N n) 0 hRQ
  let bC : ℕ → PositiveCoefficient Qh := fun n =>
    cutoffPositiveCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n) 0 hRQ
  let b'C : ℕ → PositiveCoefficient Qh := fun n =>
    cutoffPositiveCoefficient M (fun β' => H β' + (-hinf)) (β n) (N n) 0 hRQ
  -- controls
  obtain ⟨Alf⟩ := aux_limit_form_package_controls_of_bounds hd (0 : SpatialCoordinates d)
    (3 * (3 : ℝ) ^ m) hRQ S G aC Bnds
  -- the uniform defect of the infrared potentials on the closed cube
  have hcompact : IsCompact (closure (Qh : Set (SpatialCoordinates d))) :=
    lane2_isCompact_closure_centeredCube 0 hRQ
  obtain ⟨D, hD0, hD, hDbd⟩ := aux_calib_weighted_form_data_uniform_defect hinf (fun n => H (β n)) hh _ hcompact
  -- coefficient relations
  have hrepA := fun n => (cutoffPositiveCoefficient_representative M H (β n) (N n)
    (0 : SpatialCoordinates d) hRQ).2.2.2
  have hrepB := fun n => (cutoffPositiveCoefficient_representative M
    (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n) (0 : SpatialCoordinates d) hRQ).2.2.2
  have hrepB' := fun n => (cutoffPositiveCoefficient_representative M
    (fun β' => H β' + (-hinf)) (β n) (N n) (0 : SpatialCoordinates d) hRQ).2.2.2
  have hmem : ∀ᵐ x ∂volume.restrict (Qh : Set (SpatialCoordinates d)), x ∈ (Qh : Set _) :=
    ae_restrict_mem Qh.isOpen.measurableSet
  have hb' : ∀ n, (b'C n).val =ᵐ[volume.restrict (Qh : Set (SpatialCoordinates d))]
      fun x => Real.exp (aux_calib_weighted_form_data_G hinf (Qh : Set (SpatialCoordinates d)) x) * (aC n).val x := by
    intro n
    filter_upwards [hrepA n, hrepB' n, hmem] with x hA hB' hx
    rw [hB', hA, aux_calib_side_boundary_coeff_shift, aux_calib_weighted_form_data_G_of_mem hinf _ (subset_closure hx)]
    simp only [ContinuousMap.neg_apply]
    ring
  have hrel : ∀ n, ∀ᵐ x ∂volume.restrict (Qh : Set (SpatialCoordinates d)),
      Real.exp (-D n) * (b'C n).val x ≤ (bC n).val x ∧
        (bC n).val x ≤ Real.exp (D n) * (b'C n).val x := by
    intro n
    filter_upwards [hrepB n, hrepB' n, hmem] with x hB hB' hx
    have hx' : x ∈ closure (Qh : Set (SpatialCoordinates d)) := subset_closure hx
    have hfac := aux_infrared_cutoff_coefficient_reduction_factorization M H (β n) (N n) x
    have hc0 : 0 < cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n) x :=
      cutoffCoefficient_pos M _ _ _ _
    rw [hB, hB', aux_calib_side_boundary_coeff_shift, hfac]
    have := aux_calib_side_boundary_ratio_bounds
      (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n) x)
      (H (β n) x - hinf x) (D n) hc0 (hDbd n x hx')
    simp only [ContinuousMap.neg_apply]
    have hexp : Real.exp (H (β n) x) * Real.exp (-hinf x) = Real.exp (H (β n) x - hinf x) := by
      rw [← Real.exp_add]; ring_nf
    constructor
    · calc Real.exp (-D n) * (Real.exp (H (β n) x) *
            cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n) x *
            Real.exp (-hinf x))
          = Real.exp (-D n) * (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
              (β n) (N n) x * Real.exp (H (β n) x - hinf x)) := by rw [← hexp]; ring
        _ ≤ _ := this.1
    · calc cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n) x
          ≤ Real.exp (D n) * (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
              (β n) (N n) x * Real.exp (H (β n) x - hinf x)) := this.2
        _ = _ := by rw [← hexp]; ring
  -- the weight and the weighted Green limit
  obtain ⟨Kg, hKg⟩ := aux_calib_weighted_form_data_G_bounded hinf (Qh : Set (SpatialCoordinates d)) hcompact
  have hGmeas := aux_calib_weighted_form_data_G_measurable hinf (Qh : Set (SpatialCoordinates d))
  have hGN : ∀ n f, volumeResponseOperator S (aC n) f =
      (responseSolution S (aC n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1 :=
    fun n f => volumeResponseOperator_apply _ _ f
  obtain ⟨F, EF, hFconv, hFsym, hFpos, hEF, hdomEF, hEFcore, hEFform⟩ :=
    calib_weighted_green_limit hd (0 : SpatialCoordinates d) (3 * (3 : ℝ) ^ m) hRQ S hS aC bC b'C
      (aux_calib_weighted_green_limit_controls Alf)
      (fun n => volumeResponseOperator S (aC n)) G hGN hG E hE hcore Gamma
      (fun x => Real.exp (aux_calib_weighted_form_data_G hinf (Qh : Set (SpatialCoordinates d)) x))
      (aux_calib_weighted_form_data_G_continuousOn hinf _) (fun x _ => Real.exp_pos _) hb' D hD0 hD
      (fun n => (hrel n).mono fun x hx => hx.1) (fun n => (hrel n).mono fun x hx => hx.2)
  -- the weighted form and the identification of its energy with the limit of the infrared-free inverses
  obtain ⟨Eg, Gammag, hcoreg, hlocg, hweight⟩ := calib_weighted_form_data Qh E Gamma hcore hloc
    (aux_calib_weighted_form_data_G hinf (Qh : Set (SpatialCoordinates d))) hGmeas Kg hKg
  have hEg : ∀ v, Eg.toClosedForm.energy v = limitFormEnergy F v := by
    intro v
    by_cases hv : v ∈ E.toClosedForm.domain
    · have hvg : v ∈ Eg.toClosedForm.domain := hweight.domain_eq ▸ hv
      have hvf : v ∈ EF.toClosedForm.domain := hdomEF ▸ hv
      rw [← hEF v, Eg.toClosedForm.energy_of_mem hvg, EF.toClosedForm.energy_of_mem hvf,
        hweight.energy_eq v hv, hEFform v hv]
    · have hvg : v ∉ Eg.toClosedForm.domain := fun h => hv (hweight.domain_eq ▸ h)
      have hvf : v ∉ EF.toClosedForm.domain := fun h => hv (hdomEF ▸ h)
      rw [← hEF v]
      have h1 : ¬ (Eg.toClosedForm.energy v < ⊤) := fun h => hvg ((Eg.toClosedForm.energy_lt_top_iff v).1 h)
      have h2 : ¬ (EF.toClosedForm.energy v < ⊤) := fun h => hvf ((EF.toClosedForm.energy_lt_top_iff v).1 h)
      rw [not_lt_top_iff.1 h1, not_lt_top_iff.1 h2]
  -- controls for the infrared-free sequence, from those of the infrared-carrying one
  obtain ⟨Cinf, hCinf⟩ := hcompact.exists_bound_of_continuousOn hinf.continuous.continuousOn
  obtain ⟨Dsup, hDsup⟩ := hD.bddAbove_range
  have hHb : ∀ n, ∀ x ∈ closure (Qh : Set (SpatialCoordinates d)),
      |H (β n) x| ≤ |Cinf| + |Dsup| := by
    intro n x hx
    have h1 := hDbd n x hx
    have h2 : D n ≤ Dsup := hDsup ⟨n, rfl⟩
    have h3 := hCinf x hx
    rw [Real.norm_eq_abs] at h3
    calc |H (β n) x| = |(H (β n) x - hinf x) + hinf x| := by ring_nf
      _ ≤ |H (β n) x - hinf x| + |hinf x| := abs_add_le _ _
      _ ≤ |Cinf| + |Dsup| := by
          have := le_abs_self Dsup
          have := le_abs_self Cinf
          linarith
  have hrelA : ∀ n, ∀ᵐ x ∂volume.restrict (Qh : Set (SpatialCoordinates d)),
      Real.exp (-(|Cinf| + |Dsup|)) * (aC n).val x ≤ (bC n).val x ∧
        (bC n).val x ≤ Real.exp (|Cinf| + |Dsup|) * (aC n).val x := by
    intro n
    filter_upwards [hrepA n, hrepB n, hmem] with x hA hB hx
    have hfac := aux_infrared_cutoff_coefficient_reduction_factorization M H (β n) (N n) x
    have hc0 : 0 < cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n) x :=
      cutoffCoefficient_pos M _ _ _ _
    have hb := hHb n x (subset_closure hx)
    have hb1 : H (β n) x ≤ |Cinf| + |Dsup| := (le_abs_self _).trans hb
    have hb2 : -(|Cinf| + |Dsup|) ≤ H (β n) x := by have := neg_abs_le (H (β n) x); linarith
    rw [hA, hB, hfac]
    constructor
    · calc Real.exp (-(|Cinf| + |Dsup|)) * (Real.exp (H (β n) x) *
            cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n) x)
          = cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n) x *
              Real.exp (-(|Cinf| + |Dsup|) + H (β n) x) := by rw [Real.exp_add]; ring
        _ ≤ cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n) x * 1 :=
            mul_le_mul_of_nonneg_left (by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith))
              hc0.le
        _ = _ := mul_one _
    · calc cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n) x
          = cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n) x * 1 :=
            (mul_one _).symm
        _ ≤ cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n) x *
              Real.exp ((|Cinf| + |Dsup|) + H (β n) x) :=
            mul_le_mul_of_nonneg_left (by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith))
              hc0.le
        _ = Real.exp (|Cinf| + |Dsup|) * (Real.exp (H (β n) x) *
              cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n) x) := by
            rw [Real.exp_add]; ring
  have Ab := aux_limit_form_package_analytic_controls_reindex_weight Alf bC id
    (Real.exp (-(|Cinf| + |Dsup|))) (Real.exp (|Cinf| + |Dsup|)) (Real.exp_pos _)
    (Real.exp_pos _).le (fun n => (hrelA n).mono fun x hx => hx.1)
    (fun n => (hrelA n).mono fun x hx => hx.2)
  -- the boundary identification
  have hqvol : 0 < (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m) hr :
      Set (SpatialCoordinates d))).toReal := aux_thm_c1_envcal_vol_pos _ _ hr
  have hPq := centeredCube_killedPoincare (0 : SpatialCoordinates d) hr
  have hrepq := fun n => (cutoffPositiveCoefficient_representative M
    (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n) (0 : SpatialCoordinates d) hr).2.2.2
  have hAff : Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded (0 : SpatialCoordinates d) hr) hPq
      (cutoffPositiveCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n) 0 hr)
      (aux_thm_c1_envcal_e0 d (by omega)) /
      (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m) hr :
        Set (SpatialCoordinates d))).toReal) atTop
      (𝓝 (L / (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m) hr :
        Set (SpatialCoordinates d))).toReal)) :=
    hL.div_const _
  have hglb := calib_boundary_glb hd (0 : SpatialCoordinates d) ((3 : ℝ) ^ m) hr hRQ S hS
    (fun n => cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n))
    (fun n => cutoffCoefficient_continuous M _ _ _) (fun n x => cutoffCoefficient_pos M _ _ _ _)
    bC (fun n => hrepB n) (aux_calib_weighted_green_limit_controls Ab)
    (fun n => volumeResponseOperator S (bC n)) F
    (fun n f => volumeResponseOperator_apply _ _ f) hFconv Eg hEg hcoreg Gammag t alpha ht htd halpha
    halpha1 hcell hPq
    (fun n => cutoffPositiveCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (β n) (N n) 0 hr)
    (fun n => hrepq n) (aux_thm_c1_envcal_e0 d (by omega)) (L / (volume (centeredCube
      (0 : SpatialCoordinates d) ((3 : ℝ) ^ m) hr : Set (SpatialCoordinates d))).toReal) hAff
  refine ⟨Eg, Gammag, hweight, hcoreg, ?_⟩
  have hLeq : (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m) hr :
        Set (SpatialCoordinates d))).toReal * (L / (volume (centeredCube (0 : SpatialCoordinates d)
        ((3 : ℝ) ^ m) hr : Set (SpatialCoordinates d))).toReal) = L := by
    field_simp
  rw [hLeq] at hglb
  have hsInf := (hglb.1.csInf_eq hglb.2).symm
  convert hsInf using 2
  ext e
  constructor
  · rintro ⟨U, hU, Uc, h1, h2, h3, h4⟩
    exact ⟨U, Uc, hU, h1, h2, h3, h4⟩
  · rintro ⟨U, Uc, hU, h1, h2, h3, h4⟩
    exact ⟨U, hU, Uc, h1, h2, h3, h4⟩

end SubdiffusiveProcess.Paper
