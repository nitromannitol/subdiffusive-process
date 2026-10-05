module

public import SubdiffusiveProcess.Paper.lem_local_normalizations_regroup
public import SubdiffusiveProcess.Paper.prop_response_compact
public import SubdiffusiveProcess.Paper.lem_prefix_limit_atom_extraction
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Geometry.AffineFrontierNonconst

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- General-cell version of `g9_dirichlet_response_compact` (kept as its own top-level lemma, with
`z`/`r`/`hr`/`hP` as free explicit parameters instead of the fixed unit-cube values, so the
elaborator never has to rewrite the large goal via `set`). Assembled entirely from existing
pieces: `SubdiffusiveProcess.Paper.rem_bank`/`SubdiffusiveProcess.Paper.prop_16` (via `lem_local_normalizations`'s
`aux_lem_local_normalizations_test_rembank_rd_moments`/`_test_prop16_rd_band`) supply
moments/band-decay for the TRUE response; its own `regroup` machinery
(`aux_lem_local_normalizations_lnorm_proxy_hsplit`/`_hmom`/`_hband`/`_compact_transport`) transports
these into `SubdiffusiveProcess.Paper.prop_response_compact`'s hypotheses and back. No new probabilistic content. -/
theorem aux_g9_dirichlet_response_compact_general
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hrle : r ≤ 1)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (u : Fin d → ℝ) (hu : u ≠ 0) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∃ hmem : ∀ N, MemLp (fun omega : BilateralField d =>
            affineDirichletResponse (centeredCube_isBounded z hr) hP
              (cutoffPositiveCoefficient M H omega N z hr) u)
          (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun N => (hmem N).toLp (fun omega : BilateralField d =>
            affineDirichletResponse (centeredCube_isBounded z hr) hP
              (cutoffPositiveCoefficient M H omega N z hr) u)))) := by
  classical
  have hΩ : Bornology.IsBounded ((centeredCube z r hr : Opens (SpatialCoordinates d)) :
      Set (SpatialCoordinates d)) := centeredCube_isBounded z hr
  have hphi : ContDiff ℝ (⊤ : ℕ∞) (fun x : SpatialCoordinates d => ∑ i : Fin d, u i * x i) := by
    apply ContDiff.sum
    intro i _
    exact contDiff_const.mul (contDiff_apply ℝ ℝ i)
  set b := affineSobolev hΩ u 0 with hbdef
  have hbeq : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      (fun x : SpatialCoordinates d => ∑ i : Fin d, u i * x i) := by
    filter_upwards [affineL2_coeFn hΩ u 0] with x hx
    show (affineL2 hΩ u 0 : SpatialCoordinates d → ℝ) x = _
    rw [hx, affineSlope_apply, add_zero]
  have hnonconst := affine_frontier_nonconst z r hr u hu
  obtain ⟨q, delta0mom, hq, hdelta0mom, hmom_all⟩ :=
    aux_lem_local_normalizations_test_rembank_rd_moments d hd Jc Pc Xc W Sf D
  obtain ⟨delta0band, hdelta0band, hband_all⟩ :=
    aux_lem_local_normalizations_test_prop16_rd_band d hd Jc Pc Xc W Sf D
  refine ⟨min delta0mom delta0band, lt_min hdelta0mom hdelta0band, ?_⟩
  intro M Rm Sreg It H hH hM
  have hMmom : M.delta ≤ min 1 delta0mom := hM.trans (min_le_min_left 1 (min_le_left _ _))
  have hMband : M.delta ≤ min 1 delta0band := hM.trans (min_le_min_left 1 (min_le_right _ _))
  obtain ⟨Cmom6, hCmom6, hmomN⟩ :=
    hmom_all z r hr hrle hP _ hphi b hbeq M Rm Sreg It H hH hMmom
  obtain ⟨Cband, hCband, hbandN⟩ :=
    hband_all z r hr hrle hP _ hphi hnonconst b hbeq M Rm Sreg It H hH hMband
  have hRDmoment6 : ∀ N, MemLp (aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N)
      (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure := fun N => (hmomN N).1
  have hRDbound6 : ∀ N, eLpNorm (aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N)
      (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cmom6 :=
    fun N => (hmomN N).2.2.1
  set aD : ℝ := aux_lem_local_normalizations_prop16_aD d with hADdef
  have haD : 0 < aD := by
    rw [hADdef]
    unfold aux_lem_local_normalizations_prop16_aD
    have hA : (0 : ℝ) < (d : ℝ) - 1 / 2 := by
      have h2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    have hB : (d : ℝ) - 1 / 2 - (d : ℝ) + 1 = 1 / 2 := by ring
    have hC : (0 : ℝ) < (d : ℝ) - 1 / 2 + 1 := by linarith
    rw [hB]
    apply div_pos
    apply div_pos
    · exact mul_pos hA (by norm_num)
    · exact hC
    · exact mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hpq : (ENNReal.ofReal (2 : ℝ)) < ENNReal.ofReal (6 : ℝ) :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 6)).mpr (by norm_num)
  have hRfmomAll : ∀ N, MemLp (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N)
      (ENNReal.ofReal 6) (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) ∧
      eLpNorm (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N) (ENNReal.ofReal 6)
        (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) ≤
      ENNReal.ofReal Cmom6 := fun N =>
    aux_lem_local_normalizations_lnorm_proxy_hmom z r hr hP b M H hH (ENNReal.ofReal 6) N Cmom6
      hCmom6 (hRDmoment6 N) (hRDbound6 N)
  obtain ⟨hcompactRf, -, -, -, -⟩ :=
    _root_.SubdiffusiveProcess.Paper.prop_response_compact d (aux_lem_local_normalizations_lnorm_regroup_Y d)
      (aux_lem_local_normalizations_lnorm_regroup_laws M) Unit Empty
      (fun _ N => aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N)
      (fun e _ _ => e.elim)
      (ENNReal.ofReal 2) (ENNReal.ofReal 6) hpq ENNReal.ofReal_ne_top
      aD M.delta haD M.shellPrefix.delta_pos
      (fun _ => Cband) (fun _ => hCband.le)
      (fun _ => ENNReal.ofReal Cmom6) (fun _ => ENNReal.ofReal_ne_top)
      (fun _ N => by exact (hRfmomAll N).1)
      (fun _ N => by exact (hRfmomAll N).2)
      (fun _ Hband N _ => by
        simpa only [neg_mul] using aux_lem_local_normalizations_lnorm_proxy_hband z r hr hP b M H hH
          Cband aD Cmom6 hRDmoment6 hbandN Hband N)
      (fun _ Hband => by
        exact aux_lem_local_normalizations_lnorm_proxy_hsplit z r hr hP b M Hband)
      (fun e => e.elim) (fun e => e.elim)
      (fun e _ _ => e.elim)
  have hRDmem2 : ∀ N, MemLp (aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N)
      (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure :=
    fun N => (hRDmoment6 N).mono_exponent hpq.le
  have hRfmem2 : ∀ N, MemLp (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N)
      (ENNReal.ofReal 2) (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) :=
    fun N => ((hRfmomAll N).1).mono_exponent hpq.le
  have hcompact2 : IsCompact (closure (Set.range (fun N =>
      (hRfmem2 N).toLp (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N)))) := by
    have hEq : (fun N => (hRfmem2 N).toLp (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N)) =
        (fun N => (((hRfmomAll N).1).mono_exponent hpq.le).toLp
          (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N)) := rfl
    rw [hEq]
    exact hcompactRf ()
  have hcompactRD := aux_lem_local_normalizations_lnorm_proxy_compact_transport z r hr hP b M H hH
    (p := ENNReal.ofReal 2) hRDmem2 hRfmem2 hcompact2
  exact ⟨hRDmem2, hcompactRD⟩

/-- The Dirichlet-side genuine-infrared analogue of `affine_dirichlet_response_compact` (the zero-infrared result), at the unit root cell: `L²`-relative compactness of the
affine Dirichlet response family at any nonzero slope `u`, for the GENUINE infrared field `H`.
Direct specialization of `aux_g9_dirichlet_response_compact_general` at `z := 0, r := 1`. -/
theorem g9_dirichlet_response_compact
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩)
    (u : Fin d → ℝ) (hu : u ≠ 0) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∃ hmem : ∀ N, MemLp (fun omega : BilateralField d =>
            affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
              aux_lem_prefix_limit_atom_extraction_poincare.1
              (cutoffPositiveCoefficient M H omega N (0 : SpatialCoordinates d) one_pos) u)
          (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun N => (hmem N).toLp (fun omega : BilateralField d =>
            affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
              aux_lem_prefix_limit_atom_extraction_poincare.1
              (cutoffPositiveCoefficient M H omega N (0 : SpatialCoordinates d) one_pos) u)))) :=
  aux_g9_dirichlet_response_compact_general d hd Jc Pc Xc W Sf D
    (0 : SpatialCoordinates d) 1 one_pos le_rfl aux_lem_prefix_limit_atom_extraction_poincare.1 u hu

end SubdiffusiveProcess.Paper
