module

public import SubdiffusiveProcess.Paper.g9_neumann_response_compact
public import SubdiffusiveProcess.Paper.rem_bank_neumann_coercive_response_bound_uniform
public import SubdiffusiveProcess.Paper.g9_general_R_reference_split
public import SubdiffusiveProcess.Paper.lem_prefix_limit_atom_extraction
public import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_chart_transport
public import SubdiffusiveProcess.Sobolev.ScalarMultiplierCompactness
public import SubdiffusiveProcess.Analysis.GeneralRCompactness
public import SubdiffusiveProcess.Analysis.LpExponentCompact
public import SubdiffusiveProcess.Sobolev.NeumannTranslateTransfer
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

@[expose] public section




set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal ContDiff

noncomputable section
namespace Paper

/-- A smooth, nonnegative bump profile supported in `(1,2)` with unit mass, for the face-bump
source witness (a `ContDiffBump` renormalization centred at `3/2`). -/
theorem aux_g9_neumann_origin_compact_rho :
    ∃ rho : ℝ → ℝ, ContDiff ℝ ∞ rho ∧ (∀ v : ℝ, 0 ≤ rho v) ∧
      (∀ v : ℝ, v ∉ Set.Ioo (1 : ℝ) 2 → rho v = 0) ∧ (∫ v, rho v) = 1 := by
  let f : ContDiffBump (3 / 2 : ℝ) :=
    { rIn := 1 / 4, rOut := 1 / 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  refine ⟨f.normed volume, f.contDiff_normed, fun v => f.nonneg_normed v, fun v hv => ?_,
    f.integral_normed⟩
  rw [← Function.notMem_support, f.support_normed_eq, Real.ball_eq_Ioo]
  norm_num
  norm_num at hv
  exact hv

/-- A nonnegative-valued `rho` is bounded above by its maximum on its support. -/
theorem aux_g9_neumann_origin_compact_rho_bound {rho : ℝ → ℝ} (hrho0 : ∀ v : ℝ, 0 ≤ rho v)
    (hrho : ContDiff ℝ ∞ rho) (hrhos : ∀ v : ℝ, v ∉ Set.Ioo (1 : ℝ) 2 → rho v = 0) :
    ∃ M : ℝ, ∀ x : ℝ, rho x ≤ M := by
  obtain ⟨x0, -, hx0max⟩ := IsCompact.exists_isMaxOn isCompact_Icc
    (Set.nonempty_Icc.mpr (by norm_num : (1 : ℝ) ≤ 2)) hrho.continuous.continuousOn
  refine ⟨rho x0, fun x => ?_⟩
  by_cases hx : x ∈ Set.Ioo (1 : ℝ) 2
  · exact hx0max (Set.Ioo_subset_Icc_self hx)
  · rw [hrhos x hx]; exact hrho0 x0

/-- an absolute-value bound on `rho`, not needing nonnegativity. -/
theorem aux_g9_neumann_origin_compact_rho_absbound {rho : ℝ → ℝ}
    (hrho : ContDiff ℝ ∞ rho) (hrhos : ∀ v : ℝ, v ∉ Set.Ioo (1 : ℝ) 2 → rho v = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |rho x| ≤ M := by
  obtain ⟨x0, -, hx0max⟩ := IsCompact.exists_isMaxOn isCompact_Icc
    (Set.nonempty_Icc.mpr (by norm_num : (1 : ℝ) ≤ 2)) hrho.continuous.abs.continuousOn
  refine ⟨|rho x0|, abs_nonneg _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Ioo (1 : ℝ) 2
  · exact hx0max (Set.Ioo_subset_Icc_self hx)
  · rw [hrhos x hx]; simp

/-- The face-bump source `f_ε` is continuous on all of the ambient space. -/
theorem aux_g9_neumann_origin_compact_faceBump_continuous {d : ℕ} {rho : ℝ → ℝ}
    (hrho : ContDiff ℝ ∞ rho) (pvec : Fin d → ℝ) (eps : ℝ) :
    Continuous (Lane4.faceBump rho pvec eps) := by
  unfold Lane4.faceBump
  refine continuous_finset_sum _ (fun i _ => ?_)
  refine continuous_const.mul (Continuous.sub ?_ ?_)
  · exact continuous_const.mul
      (hrho.continuous.comp ((continuous_const.sub (continuous_apply i)).mul continuous_const))
  · exact continuous_const.mul
      (hrho.continuous.comp ((continuous_apply i).mul continuous_const))

/-- A uniform bound on the face-bump source, for a fixed `ε`. -/
theorem aux_g9_neumann_origin_compact_faceBump_bound {d : ℕ} {rho : ℝ → ℝ}
    (M : ℝ) (hM : 0 ≤ M) (hrhoM : ∀ x : ℝ, |rho x| ≤ M) (pvec : Fin d → ℝ) (eps : ℝ)
    (x : SpatialCoordinates d) :
    ‖Lane4.faceBump rho pvec eps x‖ ≤ (∑ i : Fin d, |pvec i|) * (2 * |eps⁻¹| * M) := by
  unfold Lane4.faceBump
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h1 : ‖(pvec i * (eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps)))‖ ≤
      |pvec i| * (|eps⁻¹| * M + |eps⁻¹| * M) := by
    rw [Real.norm_eq_abs, abs_mul]
    gcongr
    refine (abs_sub _ _).trans ?_
    gcongr
    · rw [abs_mul]; gcongr; exact hrhoM _
    · rw [abs_mul]; gcongr; exact hrhoM _
  linarith [h1]

/-- An `L²(Q)` representative of the face-bump source `f_ε`, for every `ε`. -/
theorem aux_g9_neumann_origin_compact_fL2 {d : ℕ} (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrhos : ∀ v : ℝ, v ∉ Set.Ioo (1 : ℝ) 2 → rho v = 0) (pvec : Fin d → ℝ) :
    ∃ fL2 : ℝ → DomainL2 (unitNeumannCube d), ∀ eps : ℝ, (0 < eps ∧ eps < 1 / 8) →
      ((fL2 eps : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
        faceBump rho pvec eps) := by
  obtain ⟨M, hM, hrhoM⟩ := aux_g9_neumann_origin_compact_rho_absbound hrho hrhos
  have hmem : ∀ eps : ℝ, MemLp (faceBump rho pvec eps) 2
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) := by
    intro eps
    exact MemLp.of_bound
      ((aux_g9_neumann_origin_compact_faceBump_continuous hrho pvec eps).aestronglyMeasurable)
      ((∑ i : Fin d, |pvec i|) * (2 * |eps⁻¹| * M))
      (Filter.Eventually.of_forall
        (aux_g9_neumann_origin_compact_faceBump_bound M hM hrhoM pvec eps))
  exact ⟨fun eps => (hmem eps).toLp (faceBump rho pvec eps),
    fun eps _ => (hmem eps).coeFn_toLp⟩

/-- At shift `m = 0` the chart-transport reference factor collapses to the bare
exponential (the `κ`-ratio is `1`). -/
theorem aux_g9_neumann_origin_compact_reference_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (z : SpatialCoordinates d) (om : BilateralField d) :
    aux_g9chart_transport_reference M H N 0 z om =
      Real.exp (H om z + aux_g9chart_transport_retained 0 z om) := by
  have hz : ((N : ℤ) - (0 : ℤ)).toNat = N := by simp
  have hpos : 0 < aux_g9chart_transport_kappa M N := by
    unfold aux_g9chart_transport_kappa
    have := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
    positivity
  unfold aux_g9chart_transport_reference
  rw [hz, div_self hpos.ne', one_mul]

/-- The positive coefficient built from `cutoffCoefficient` agrees a.e. with it on its cube. -/
theorem aux_g9_neumann_origin_compact_coeff_ae {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ) (z : SpatialCoordinates d) :
    ((cutoffPositiveCoefficient M H om N z one_pos).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))]
      cutoffCoefficient M H om N := by
  haveI : Fact ((centeredCube z 1 one_pos : Set (SpatialCoordinates d)) ⊆
      (closedCube z 1 one_pos : Set (SpatialCoordinates d))) :=
    ⟨centeredCube_subset_closedCube z one_pos⟩
  have h0 := normalizedContinuousPositiveCoefficient_coeFn (Ω := centeredCube z 1 one_pos)
    (closedCube z 1 one_pos) (cutoffCoefficientCM M H om N z one_pos)
    (cutoffCoefficientCM_pos M H om N z one_pos) 1 one_pos
  filter_upwards [h0, ae_restrict_mem (centeredCube z 1 one_pos).isOpen.measurableSet]
    with x hx hxmem
  have h := hx hxmem
  unfold cutoffPositiveCoefficient
  rw [div_one] at h
  exact h



theorem aux_g9_neumann_origin_compact_identity {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (hPn : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(w : SobolevData (unitNeumannCube d)).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w‖)
    (N : ℕ) (q : Fin d → ℝ) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
          (cutoffPositiveCoefficient M H
            (aux_g9chart_transport_S 0 (fun _ : Fin d => (1 / 2 : ℝ)) omega) N 0 one_pos) q =
        Real.exp ((H omega) (fun _ : Fin d => (1 / 2 : ℝ)) +
            aux_g9chart_transport_retained 0 (fun _ : Fin d => (1 / 2 : ℝ)) omega) *
          affineInverseNeumannResponse hPn
            (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) q := by
  let v : SpatialCoordinates d := fun _ : Fin d => (1 / 2 : ℝ)
  have htrans := aux_g9chart_transport_coefficient M 0 v hH N (by exact_mod_cast Nat.zero_le N)
  filter_upwards [htrans] with om hom
  have hfg : ∀ y : SpatialCoordinates d, cutoffCoefficient M H om N (v + y) =
      Real.exp (H om v + aux_g9chart_transport_retained 0 v om) *
        cutoffCoefficient M H (aux_g9chart_transport_S 0 v om) N y := by
    intro y
    have h1 := hom y
    simp only [neg_zero, zpow_zero, one_smul, sub_zero, Int.toNat_natCast] at h1
    rwa [aux_g9_neumann_origin_compact_reference_eq] at h1
  have hc : (0 : ℝ) < Real.exp (H om v + aux_g9chart_transport_retained 0 v om) := Real.exp_pos _
  let hcoeff0 : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos) :=
    cutoffPositiveCoefficient M H (aux_g9chart_transport_S 0 v om) N 0 one_pos
  have haP : (hcoeff0.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))]
      cutoffCoefficient M H (aux_g9chart_transport_S 0 v om) N :=
    aux_g9_neumann_origin_compact_coeff_ae M H (aux_g9chart_transport_S 0 v om) N 0
  let hcoeffU : PositiveCoefficient (unitNeumannCube d) :=
    cutoffPositiveCoefficient M H om N v one_pos
  have hbP : (hcoeffU.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
      cutoffCoefficient M H om N :=
    aux_g9_neumann_origin_compact_coeff_ae M H om N v
  exact affineInverseNeumannResponse_origin_eq_unit (cutoffCoefficient M H om N)
    (cutoffCoefficient M H (aux_g9chart_transport_S 0 v om) N)
    (Lane4.cutoffCoefficient_continuous M H om N)
    (Lane4.cutoffCoefficient_continuous M H (aux_g9chart_transport_S 0 v om) N)
    (Lane4.cutoffCoefficient_pos M H om N)
    (Lane4.cutoffCoefficient_pos M H (aux_g9chart_transport_S 0 v om) N)
    _ hc hfg
    aux_lem_prefix_limit_atom_extraction_poincare.2 hPn
    hcoeff0 haP hcoeffU hbP q



theorem aux_g9_neumann_origin_compact_unit_compact {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [Fact (1 ≤ ENNReal.ofReal 2)]
    (E : Paper.in_J d) (P : Paper.in_poincare d hd E) (X : Paper.in_extension d hd E)
    (W : Lane4.SmallPerturbationInput d) (D : Paper.lane4_deterministic_good_scale_input d)
    (Sfi : Lane4.SobolevFoundationalInput d hd) (Cresp : ℝ) (hCresp : 0 < Cresp)
    (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho) (hrho0 : ∀ v : ℝ, 0 ≤ rho v)
    (hrhos : ∀ v : ℝ, v ∉ Set.Ioo (1 : ℝ) 2 → rho v = 0) (hrhoI : ∫ v, rho v = 1)
    (pvec : Fin d → ℝ) (hpvec : ∑ i, pvec i ^ 2 = 1)
    (hPn : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(w : SobolevData (unitNeumannCube d)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w‖)
    (fL2 : ℝ → DomainL2 (unitNeumannCube d))
    (hfL2 : ∀ eps : ℝ, (0 < eps ∧ eps < 1 / 8) →
      ((fL2 eps : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
        faceBump rho pvec eps)) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
        M.delta ≤ min 1 delta1 →
        (∃ hmemY : ∀ N, MemLp (fun omega : BilateralField d => affineInverseNeumannResponse hPn
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) pvec)
            (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure,
          IsCompact (closure (Set.range fun N => (hmemY N).toLp
            (fun omega : BilateralField d => affineInverseNeumannResponse hPn
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) pvec)))) ∧
        (∃ B4 : ℝ, 0 ≤ B4 ∧ ∀ N, MemLp (fun omega : BilateralField d =>
              affineInverseNeumannResponse hPn
                (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) pvec)
            4 (chaosSampleLaw M).toMeasure ∧
          eLpNorm (fun omega : BilateralField d => affineInverseNeumannResponse hPn
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) pvec)
            4 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B4) := by
  obtain ⟨delta1a, hdelta1a_pos, hstep3⟩ :=
    aux_g9_neumann_response_compact_general d hd E P X W D Sfi Cresp hCresp
      ((d : ℝ) - 1 / 2) (by linarith) (by linarith)
      rho hrho hrho0 hrhos hrhoI pvec hpvec hPn fL2 hfL2
  obtain ⟨delta0b, hdelta0b_pos, B4, hB4nonneg, hstep4⟩ :=
    rem_bank_neumann_coercive_response_bound_uniform d hd E P Sfi 1 le_rfl
      rho hrho hrho0 hrhos hrhoI pvec hpvec hPn
  refine ⟨min delta1a delta0b, lt_min hdelta1a_pos hdelta0b_pos, ?_⟩
  intro M Rm hRmC Sreg It H hH hMdelta
  have hMdelta1 : M.delta ≤ min 1 delta1a := hMdelta.trans (by gcongr; exact min_le_left _ _)
  have hMdelta0 : M.delta ≤ min 1 delta0b := hMdelta.trans (by gcongr; exact min_le_right _ _)
  obtain ⟨hmem2, hcompact2⟩ := hstep3 M Rm hRmC Sreg It H hH hMdelta1
  obtain ⟨Kcoerc, hKcoerc, hmem4, heLp4⟩ := hstep4 M Rm H hH hMdelta0
  have heq4 : ENNReal.ofReal (4 * 1) = (4 : ℝ≥0∞) := by norm_num
  constructor
  · exact ⟨hmem2, hcompact2⟩
  · refine ⟨B4, hB4nonneg, fun N => ⟨?_, ?_⟩⟩
    · have h := (hmem4 N).2; rwa [heq4] at h
    · have h := (heLp4 N).2; rwa [heq4] at h

/-- Hölder triple `(4,4,2)`: `1/4 + 1/4 = 1/2`, used for `‖cY‖₂ ≤ ‖c‖₄‖Y‖₄`. -/
theorem aux_g9_neumann_origin_compact_holder442 : ENNReal.HolderTriple 4 4 2 := by
  refine ⟨?_⟩
  have e4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by norm_num
  have e2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
  rw [e4, e2, ← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 4),
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- The unit-cube inverse-Neumann response family, as a bare function of `(N, ω)`. -/
def aux_g9_neumann_origin_compact_Y {d : ℕ}
    (hPn : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(w : SobolevData (unitNeumannCube d)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w‖)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (pvec : Fin d → ℝ) (N : ℕ) (omega : BilateralField d) : ℝ :=
  affineInverseNeumannResponse hPn
    (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) pvec

/-- The chart-transport scalar factor `c(ω) = exp(H(ω)(v) + retained(0,v,ω))`. -/
def aux_g9_neumann_origin_compact_c {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) : ℝ :=
  Real.exp ((H omega) (fun _ : Fin d => (1 / 2 : ℝ)) +
    aux_g9chart_transport_retained 0 (fun _ : Fin d => (1 / 2 : ℝ)) omega)

theorem aux_g9_neumann_origin_compact_shifted_compact {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [Fact (1 ≤ ENNReal.ofReal 2)]
    (pvec : Fin d → ℝ)
    (hPn : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(w : SobolevData (unitNeumannCube d)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w‖)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (delta1 : ℝ) (hdelta1_pos : 0 < delta1) (hMdelta : M.delta ≤ min 1 delta1)
    (hmemY : ∀ N, MemLp (aux_g9_neumann_origin_compact_Y hPn M H pvec N) (ENNReal.ofReal 2)
      (chaosSampleLaw M).toMeasure)
    (hcompactY : IsCompact (closure (Set.range fun N =>
      (hmemY N).toLp (aux_g9_neumann_origin_compact_Y hPn M H pvec N))))
    (B4 : ℝ) (hB4 : 0 ≤ B4)
    (hmem4Y : ∀ N, MemLp (aux_g9_neumann_origin_compact_Y hPn M H pvec N) 4
      (chaosSampleLaw M).toMeasure)
    (heLp4Y : ∀ N, eLpNorm (aux_g9_neumann_origin_compact_Y hPn M H pvec N) 4
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B4) :
    ∃ B2 : ℝ, 0 ≤ B2 ∧
      ∃ hmemZ : ∀ N, MemLp (fun omega => aux_g9_neumann_origin_compact_c M H omega *
          aux_g9_neumann_origin_compact_Y hPn M H pvec N omega) 1 (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range fun N => (hmemZ N).toLp (fun omega =>
          aux_g9_neumann_origin_compact_c M H omega *
            aux_g9_neumann_origin_compact_Y hPn M H pvec N omega))) ∧
        ∀ N, MemLp (fun omega => aux_g9_neumann_origin_compact_c M H omega *
              aux_g9_neumann_origin_compact_Y hPn M H pvec N omega) 2 (chaosSampleLaw M).toMeasure ∧
          eLpNorm (fun omega => aux_g9_neumann_origin_compact_c M H omega *
              aux_g9_neumann_origin_compact_Y hPn M H pvec N omega) 2 (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal B2 := by
  have hpq12 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by norm_num
  have hmemY1 : ∀ N, MemLp (aux_g9_neumann_origin_compact_Y hPn M H pvec N) 1
      (chaosSampleLaw M).toMeasure := fun N => (hmemY N).mono_exponent hpq12
  have hcompactY1 : IsCompact (closure (Set.range fun N =>
      (hmemY1 N).toLp (aux_g9_neumann_origin_compact_Y hPn M H pvec N))) :=
    isCompact_closure_range_mono_exponent (μ := (chaosSampleLaw M).toMeasure) hpq12 hmemY hcompactY
  have hv01 : (fun _ : Fin d => (1 / 2 : ℝ)) ∈
      {x : SpatialCoordinates d | ∀ i, 0 ≤ x i ∧ x i ≤ 1} := by
    intro i; constructor <;> norm_num
  have hcref := g9_general_R_reference_split hd M Rm H hH (min 1 delta1)
    (lt_min one_pos hdelta1_pos) (min_le_left _ _) hMdelta 0 (fun _ : Fin d => (1 / 2 : ℝ)) hv01
  have hmemc4 : MemLp (aux_g9_neumann_origin_compact_c M H) 4 (chaosSampleLaw M).toMeasure :=
    hcref.1
  haveI := aux_g9_neumann_origin_compact_holder442
  have hmemZ2 : ∀ N, MemLp (fun omega => aux_g9_neumann_origin_compact_c M H omega *
      aux_g9_neumann_origin_compact_Y hPn M H pvec N omega) 2 (chaosSampleLaw M).toMeasure :=
    fun N => MemLp.mul' hmemc4 (hmem4Y N)
  have hmemZ1 : ∀ N, MemLp (fun omega => aux_g9_neumann_origin_compact_c M H omega *
      aux_g9_neumann_origin_compact_Y hPn M H pvec N omega) 1 (chaosSampleLaw M).toMeasure :=
    fun N => (hmemZ2 N).mono_exponent (by norm_num)
  have hmemY2 : ∀ N, MemLp (aux_g9_neumann_origin_compact_Y hPn M H pvec N) 2
      (chaosSampleLaw M).toMeasure := fun N => (hmem4Y N).mono_exponent (by norm_num)
  have heLp2Y : ∀ N, eLpNorm (aux_g9_neumann_origin_compact_Y hPn M H pvec N) 2
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B4 := fun N =>
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)).trans (heLp4Y N)
  have hcompactZ1 : IsCompact (closure (Set.range fun N => (hmemZ1 N).toLp (fun omega =>
      aux_g9_neumann_origin_compact_c M H omega *
        aux_g9_neumann_origin_compact_Y hPn M H pvec N omega))) :=
    isCompact_closure_range_smul_of_memLp_higher (aux_g9_neumann_origin_compact_c M H)
      (by norm_num) (by norm_num) hmemc4 (aux_g9_neumann_origin_compact_Y hPn M H pvec)
      hmemY1 hmemY2 B4 hB4 heLp2Y hmemZ1 hcompactY1
  have hNcnn : 0 ≤ (eLpNorm (aux_g9_neumann_origin_compact_c M H) 4
      (chaosSampleLaw M).toMeasure).toReal := ENNReal.toReal_nonneg
  have hNctop : eLpNorm (aux_g9_neumann_origin_compact_c M H) 4 (chaosSampleLaw M).toMeasure ≠ ⊤ :=
    hmemc4.eLpNorm_lt_top.ne
  refine ⟨(eLpNorm (aux_g9_neumann_origin_compact_c M H) 4 (chaosSampleLaw M).toMeasure).toReal *
    B4, mul_nonneg hNcnn hB4, hmemZ1, hcompactZ1, fun N => ⟨hmemZ2 N, ?_⟩⟩
  have hraw := eLpNorm_smul_le_mul_eLpNorm (r := (2 : ℝ≥0∞)) (p := (4 : ℝ≥0∞)) (q := (4 : ℝ≥0∞))
    hmemc4.aestronglyMeasurable (hmem4Y N).aestronglyMeasurable
  have heqcY : (aux_g9_neumann_origin_compact_c M H • aux_g9_neumann_origin_compact_Y hPn M H
      pvec N) = fun omega => aux_g9_neumann_origin_compact_c M H omega *
        aux_g9_neumann_origin_compact_Y hPn M H pvec N omega := by
    funext omega; exact smul_eq_mul _ _
  rw [heqcY] at hraw
  have hstep : eLpNorm (fun omega => aux_g9_neumann_origin_compact_c M H omega *
        aux_g9_neumann_origin_compact_Y hPn M H pvec N omega) 2 (chaosSampleLaw M).toMeasure ≤
      eLpNorm (aux_g9_neumann_origin_compact_c M H) 4 (chaosSampleLaw M).toMeasure *
        eLpNorm (aux_g9_neumann_origin_compact_Y hPn M H pvec N) 4 (chaosSampleLaw M).toMeasure :=
    hraw
  refine hstep.trans ?_
  calc eLpNorm (aux_g9_neumann_origin_compact_c M H) 4 (chaosSampleLaw M).toMeasure *
        eLpNorm (aux_g9_neumann_origin_compact_Y hPn M H pvec N) 4 (chaosSampleLaw M).toMeasure
      ≤ eLpNorm (aux_g9_neumann_origin_compact_c M H) 4 (chaosSampleLaw M).toMeasure *
          ENNReal.ofReal B4 := by gcongr; exact heLp4Y N
    _ = ENNReal.ofReal (eLpNorm (aux_g9_neumann_origin_compact_c M H) 4
          (chaosSampleLaw M).toMeasure).toReal * ENNReal.ofReal B4 := by
        rw [ENNReal.ofReal_toReal hNctop]
    _ = ENNReal.ofReal ((eLpNorm (aux_g9_neumann_origin_compact_c M H) 4
          (chaosSampleLaw M).toMeasure).toReal * B4) := (ENNReal.ofReal_mul hNcnn).symm

theorem aux_g9_neumann_origin_compact_S_cancel {d : ℕ} (v : SpatialCoordinates d)
    (om : BilateralField d) :
    aux_g9chart_transport_S 0 v (aux_g9chart_transport_S 0 (-v) om) = om := by
  funext i
  apply ContinuousMap.ext
  intro y
  have h1 : aux_g9chart_transport_S 0 v (aux_g9chart_transport_S 0 (-v) om) i y
      = (aux_g9chart_transport_S 0 (-v) om) i (v + y) := by
    rw [aux_g9chart_transport_S_apply]
    simp only [sub_zero, neg_zero, zpow_zero, one_smul]
  rw [h1, aux_g9chart_transport_S_apply]
  simp only [sub_zero, neg_zero, zpow_zero, one_smul]
  congr 1
  abel

/-- The origin-cube inverse-Neumann response family. -/
def aux_g9_neumann_origin_compact_X {d : ℕ} [NeZero d] (pvec : Fin d → ℝ)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (omega : BilateralField d) : ℝ :=
  affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
    (cutoffPositiveCoefficient M H omega N 0 one_pos) pvec

theorem aux_g9_neumann_origin_compact_X_ae {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (hPn : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(w : SobolevData (unitNeumannCube d)).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w‖)
    (N : ℕ) (pvec : Fin d → ℝ) :
    aux_g9_neumann_origin_compact_X pvec M H N =ᵐ[(chaosSampleLaw M).toMeasure]
      (fun omega => aux_g9_neumann_origin_compact_c M H omega *
        aux_g9_neumann_origin_compact_Y hPn M H pvec N omega) ∘
        aux_g9chart_transport_S 0 (-(fun _ : Fin d => (1 / 2 : ℝ))) := by
  have h_id := aux_g9_neumann_origin_compact_identity M H hH hPn N pvec
  have hSneg := (aux_g9chart_transport_S_measurePreserving M 0
    (-(fun _ : Fin d => (1 / 2 : ℝ)))).quasiMeasurePreserving
  have hpull := hSneg.ae h_id
  filter_upwards [hpull] with omega' homega'
  rw [aux_g9_neumann_origin_compact_S_cancel] at homega'
  exact homega'

/-- Step C: the origin-cube family `X` inherits `L¹`-compactness and a uniform `L²` bound from
the shifted `L¹`-compact, `L²`-bounded family `Z = c·Y` of Step B, by pulling back along the
measure-preserving shift `S_{-v}`. -/
theorem aux_g9_neumann_origin_compact_origin_compact {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (pvec : Fin d → ℝ)
    (hPn : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(w : SobolevData (unitNeumannCube d)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w‖)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (B2 : ℝ)
    (hmemZ : ∀ N, MemLp (fun omega => aux_g9_neumann_origin_compact_c M H omega *
      aux_g9_neumann_origin_compact_Y hPn M H pvec N omega) 1 (chaosSampleLaw M).toMeasure)
    (hcompactZ : IsCompact (closure (Set.range fun N => (hmemZ N).toLp (fun omega =>
      aux_g9_neumann_origin_compact_c M H omega *
        aux_g9_neumann_origin_compact_Y hPn M H pvec N omega))))
    (hboundZ : ∀ N, MemLp (fun omega => aux_g9_neumann_origin_compact_c M H omega *
          aux_g9_neumann_origin_compact_Y hPn M H pvec N omega) 2 (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun omega => aux_g9_neumann_origin_compact_c M H omega *
          aux_g9_neumann_origin_compact_Y hPn M H pvec N omega) 2 (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal B2) :
    ∃ hmemX : ∀ N, MemLp (aux_g9_neumann_origin_compact_X pvec M H N) 1
        (chaosSampleLaw M).toMeasure,
      IsCompact (closure (Set.range fun N =>
        (hmemX N).toLp (aux_g9_neumann_origin_compact_X pvec M H N))) ∧
      ∀ N, MemLp (aux_g9_neumann_origin_compact_X pvec M H N) 2 (chaosSampleLaw M).toMeasure ∧
        eLpNorm (aux_g9_neumann_origin_compact_X pvec M H N) 2 (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal B2 := by
  have hS : MeasureTheory.MeasurePreserving
      (aux_g9chart_transport_S 0 (-(fun _ : Fin d => (1 / 2 : ℝ))))
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure :=
    aux_g9chart_transport_S_measurePreserving M 0 (-(fun _ : Fin d => (1 / 2 : ℝ)))
  have hXae := aux_g9_neumann_origin_compact_X_ae M H hH hPn
  have hmemcomp : ∀ N, MemLp ((fun omega => aux_g9_neumann_origin_compact_c M H omega *
      aux_g9_neumann_origin_compact_Y hPn M H pvec N omega) ∘
      aux_g9chart_transport_S 0 (-(fun _ : Fin d => (1 / 2 : ℝ)))) 1 (chaosSampleLaw M).toMeasure :=
    fun N => (hmemZ N).comp_measurePreserving hS
  have hmemX : ∀ N, MemLp (aux_g9_neumann_origin_compact_X pvec M H N) 1
      (chaosSampleLaw M).toMeasure :=
    fun N => (hmemcomp N).ae_eq (hXae N pvec).symm
  refine ⟨hmemX, ?_, ?_⟩
  · have hcompactcomp := aux_compact_comp_measurePreserving
      (aux_g9chart_transport_S 0 (-(fun _ : Fin d => (1 / 2 : ℝ)))) hS
      (fun N omega => aux_g9_neumann_origin_compact_c M H omega *
        aux_g9_neumann_origin_compact_Y hPn M H pvec N omega) hmemZ hcompactZ
    have heqrange : (fun N => (hmemX N).toLp (aux_g9_neumann_origin_compact_X pvec M H N)) =
        (fun N => (hmemcomp N).toLp ((fun omega => aux_g9_neumann_origin_compact_c M H omega *
          aux_g9_neumann_origin_compact_Y hPn M H pvec N omega) ∘
          aux_g9chart_transport_S 0 (-(fun _ : Fin d => (1 / 2 : ℝ))))) := by
      funext N
      exact MemLp.toLp_congr (hmemX N) (hmemcomp N) (hXae N pvec)
    rw [heqrange]
    exact hcompactcomp
  · intro N
    have hXaeN := hXae N pvec
    have hmem2 : MemLp (aux_g9_neumann_origin_compact_X pvec M H N) 2 (chaosSampleLaw M).toMeasure :=
      ((hboundZ N).1.comp_measurePreserving hS).ae_eq hXaeN.symm
    refine ⟨hmem2, ?_⟩
    rw [eLpNorm_congr_ae hXaeN, eLpNorm_comp_measurePreserving (hboundZ N).1.aestronglyMeasurable hS]
    exact (hboundZ N).2

/-- Step D: rescaling the slope `pvec ↦ u = t • pvec` multiplies the origin-cube response family
by the fixed constant `t²`, so it stays `L¹`-compact with a rescaled uniform `L²` bound. -/
theorem aux_g9_neumann_origin_compact_rescale {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (pvec u : Fin d → ℝ) (t : ℝ) (ht : u = t • pvec)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (B2 : ℝ) (hB2 : 0 ≤ B2)
    (hmemX : ∀ N, MemLp (aux_g9_neumann_origin_compact_X pvec M H N) 1 (chaosSampleLaw M).toMeasure)
    (hcompactX : IsCompact (closure (Set.range fun N =>
      (hmemX N).toLp (aux_g9_neumann_origin_compact_X pvec M H N))))
    (hboundX : ∀ N, MemLp (aux_g9_neumann_origin_compact_X pvec M H N) 2
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (aux_g9_neumann_origin_compact_X pvec M H N) 2 (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal B2) :
    ∃ hmemXu : ∀ N, MemLp (aux_g9_neumann_origin_compact_X u M H N) 1 (chaosSampleLaw M).toMeasure,
      IsCompact (closure (Set.range fun N =>
        (hmemXu N).toLp (aux_g9_neumann_origin_compact_X u M H N))) ∧
      ∃ B2' : ℝ, 0 ≤ B2' ∧ ∀ N, MemLp (aux_g9_neumann_origin_compact_X u M H N) 2
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm (aux_g9_neumann_origin_compact_X u M H N) 2 (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal B2' := by
  have hXu_eq : ∀ N, aux_g9_neumann_origin_compact_X u M H N = fun omega =>
      t ^ 2 * aux_g9_neumann_origin_compact_X pvec M H N omega := by
    intro N
    funext omega
    show aux_g9_neumann_origin_compact_X u M H N omega =
      t ^ 2 * aux_g9_neumann_origin_compact_X pvec M H N omega
    unfold aux_g9_neumann_origin_compact_X
    rw [ht]
    exact affineInverseNeumannResponse_smul_slope aux_lem_prefix_limit_atom_extraction_poincare.2 _ t pvec
  have hXu_smul : ∀ N, aux_g9_neumann_origin_compact_X u M H N = t ^ 2 •
      aux_g9_neumann_origin_compact_X pvec M H N := by
    intro N; rw [hXu_eq N]; funext omega; exact (smul_eq_mul _ _).symm
  have hmemXu : ∀ N, MemLp (aux_g9_neumann_origin_compact_X u M H N) 1
      (chaosSampleLaw M).toMeasure := by
    intro N; rw [hXu_smul N]; exact (hmemX N).const_smul (t ^ 2)
  refine ⟨hmemXu, ?_, |t ^ 2| * B2, mul_nonneg (abs_nonneg _) hB2, ?_⟩
  · have hcs := isCompact_closure_range_bounded_scalar_smul
      (fun N => (hmemX N).toLp (aux_g9_neumann_origin_compact_X pvec M H N)) hcompactX
      (fun _ => t ^ 2) |t ^ 2| (fun _ => le_refl _)
    have heqrange : (fun N => (hmemXu N).toLp (aux_g9_neumann_origin_compact_X u M H N)) =
        (fun N => t ^ 2 • (hmemX N).toLp (aux_g9_neumann_origin_compact_X pvec M H N)) := by
      funext N
      rw [← MemLp.toLp_const_smul]
      exact MemLp.toLp_congr (hmemXu N) ((hmemX N).const_smul (t ^ 2)) (by rw [hXu_smul N])
    rw [heqrange]
    exact hcs
  · intro N
    have hmemXu2 : MemLp (aux_g9_neumann_origin_compact_X u M H N) 2
        (chaosSampleLaw M).toMeasure := by
      rw [hXu_smul N]; exact (hboundX N).1.const_smul (t ^ 2)
    refine ⟨hmemXu2, ?_⟩
    have hraw : eLpNorm (t ^ 2 • aux_g9_neumann_origin_compact_X pvec M H N) 2
        (chaosSampleLaw M).toMeasure =
        ‖(t ^ 2 : ℝ)‖ₑ * eLpNorm (aux_g9_neumann_origin_compact_X pvec M H N) 2
          (chaosSampleLaw M).toMeasure :=
      eLpNorm_const_smul (t ^ 2) (aux_g9_neumann_origin_compact_X pvec M H N) 2
        (chaosSampleLaw M).toMeasure
    rw [eLpNorm_congr_ae (Filter.EventuallyEq.of_eq (hXu_smul N)), hraw,
      Real.enorm_eq_ofReal_abs]
    calc ENNReal.ofReal |t ^ 2| * eLpNorm (aux_g9_neumann_origin_compact_X pvec M H N) 2
          (chaosSampleLaw M).toMeasure
        ≤ ENNReal.ofReal |t ^ 2| * ENNReal.ofReal B2 := by gcongr; exact (hboundX N).2
      _ = ENNReal.ofReal (|t ^ 2| * B2) := (ENNReal.ofReal_mul (abs_nonneg _)).symm

/-- Isolated helper: builds `pvec`'s face-bump witness `(rho, fL2)` in a MINIMAL local context
(just `pvec`), so downstream callers can `obtain` the already-elaborated composite result
instead of destructuring two nested existentials inside a large proof context (this avoids a
`whnf` heartbeat timeout observed when the two `obtain`s ran directly inside the principal). -/
theorem aux_g9_neumann_origin_compact_fL2_witness {d : ℕ} (pvec : Fin d → ℝ) :
    ∃ rho : ℝ → ℝ, ContDiff ℝ ∞ rho ∧ (∀ v : ℝ, 0 ≤ rho v) ∧
      (∀ v : ℝ, v ∉ Set.Ioo (1 : ℝ) 2 → rho v = 0) ∧ (∫ v, rho v) = 1 ∧
      ∃ fL2 : ℝ → DomainL2 (unitNeumannCube d), ∀ eps : ℝ, (0 < eps ∧ eps < 1 / 8) →
        ((fL2 eps : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
          faceBump rho pvec eps) := by
  obtain ⟨rho, hrho, hrho0, hrhos, hrhoI⟩ := aux_g9_neumann_origin_compact_rho
  obtain ⟨fL2, hfL2⟩ := aux_g9_neumann_origin_compact_fL2 rho hrho hrhos pvec
  exact ⟨rho, hrho, hrho0, hrhos, hrhoI, fL2, hfL2⟩



theorem g9_neumann_origin_compact (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : Paper.in_J d) (P : Paper.in_poincare d hd E) (X : Paper.in_extension d hd E)
    (W : Lane4.SmallPerturbationInput d) (D : Paper.lane4_deterministic_good_scale_input d)
    (Sfi : Lane4.SobolevFoundationalInput d hd) (Cresp : ℝ) (hCresp : 0 < Cresp)
    (u : Fin d → ℝ) (hu : u ≠ 0) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
        M.delta ≤ min 1 delta1 →
        ∃ hmem : ∀ N, MemLp (fun omega : BilateralField d =>
            affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
              (cutoffPositiveCoefficient M H omega N 0 one_pos) u) 1 (chaosSampleLaw M).toMeasure,
          IsCompact (closure (Set.range (fun N => (hmem N).toLp (fun omega : BilateralField d =>
            affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
              (cutoffPositiveCoefficient M H omega N 0 one_pos) u)))) ∧
          ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (fun omega : BilateralField d =>
              affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
                (cutoffPositiveCoefficient M H omega N 0 one_pos) u) 2 (chaosSampleLaw M).toMeasure ∧
            eLpNorm (fun omega : BilateralField d =>
              affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
                (cutoffPositiveCoefficient M H omega N 0 one_pos) u) 2 (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal B := by
  haveI hFact2 : Fact (1 ≤ ENNReal.ofReal 2) := ⟨by norm_num⟩
  have hex0 : ∃ i0, u i0 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hu (funext fun i => hcon i)
  obtain ⟨i0, hi0⟩ := hex0
  have hspos : 0 < ∑ i, u i ^ 2 :=
    Finset.sum_pos' (fun i _ => sq_nonneg (u i)) ⟨i0, Finset.mem_univ i0, sq_pos_of_ne_zero hi0⟩
  let s : ℝ := ∑ i, u i ^ 2
  let pvec : Fin d → ℝ := (Real.sqrt s)⁻¹ • u
  have hpvec_apply : ∀ i, pvec i = (Real.sqrt s)⁻¹ * u i := by
    intro i; show ((Real.sqrt s)⁻¹ • u) i = (Real.sqrt s)⁻¹ * u i
    rw [Pi.smul_apply, smul_eq_mul]
  have hsqrt_ne : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hspos).ne'
  have hsqrt_sq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hspos.le
  have hpvec : ∑ i, pvec i ^ 2 = 1 := by
    have : ∀ i, pvec i ^ 2 = (Real.sqrt s)⁻¹ ^ 2 * u i ^ 2 := by
      intro i; rw [hpvec_apply]; ring
    simp only [this, ← Finset.mul_sum]
    rw [inv_pow, hsqrt_sq, inv_mul_cancel₀ hspos.ne']
  have hu_eq : u = Real.sqrt s • pvec := by
    show u = Real.sqrt s • ((Real.sqrt s)⁻¹ • u)
    rw [smul_smul, mul_inv_cancel₀ hsqrt_ne, one_smul]
  clear_value pvec s
  obtain ⟨rho, hrho, hrho0, hrhos, hrhoI, fL2, hfL2⟩ :=
    aux_g9_neumann_origin_compact_fL2_witness pvec
  have hPn : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(w : SobolevData (unitNeumannCube d)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w‖ :=
    aux_lem_prefix_limit_atom_extraction_poincareN.2
  have hstepA_full := aux_g9_neumann_origin_compact_unit_compact hd E P X W D
    Sfi Cresp hCresp rho hrho hrho0 hrhos hrhoI pvec hpvec hPn fL2 hfL2
  obtain ⟨delta1, hdelta1_pos, hstepA⟩ := hstepA_full
  refine ⟨delta1, hdelta1_pos, ?_⟩
  intro M Rm hRmC Sreg It H hH hMdelta
  have hstepA_at := hstepA M Rm hRmC Sreg It H hH hMdelta
  obtain ⟨⟨hmemY, hcompactY⟩, B4, hB4, hbound4⟩ := hstepA_at
  have hstepB_full := aux_g9_neumann_origin_compact_shifted_compact hd pvec hPn M Rm H hH delta1
    hdelta1_pos hMdelta hmemY hcompactY B4 hB4 (fun N => (hbound4 N).1) (fun N => (hbound4 N).2)
  obtain ⟨B2, hB2, hmemZ, hcompactZ, hboundZ⟩ := hstepB_full
  have hstepC_full :=
    aux_g9_neumann_origin_compact_origin_compact pvec hPn M H hH B2 hmemZ hcompactZ hboundZ
  obtain ⟨hmemX, hcompactX, hboundX⟩ := hstepC_full
  have hstepD_full := aux_g9_neumann_origin_compact_rescale pvec u (Real.sqrt s) hu_eq M H B2 hB2
    hmemX hcompactX hboundX
  obtain ⟨hmemXu, hcompactXu, B2', hB2', hboundXu⟩ := hstepD_full
  exact ⟨hmemXu, hcompactXu, B2', hB2', hboundXu⟩

end Paper
