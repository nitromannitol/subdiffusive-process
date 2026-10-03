module

public import SubdiffusiveProcess.Paper.g9_sigma_entries_compact
public import SubdiffusiveProcess.Paper.g9_sigma_entries_l2_uniform
public import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_chart_transport
public import SubdiffusiveProcess.Paper.g9_neumann_origin_compact
public import SubdiffusiveProcess.Analysis.LpExponentCompact
public import SubdiffusiveProcess.Analysis.UniformLpBound

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4 Homogenization
open scoped ENNReal NNReal

noncomputable section
namespace Paper

variable {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]



def aux_g9_origin_entry_package_neumannInput {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Cresp : ℝ) (u : Fin d → ℝ) : Prop :=
  ∃ delta1 : ℝ, 0 < delta1 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
    ∀ (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M I Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      M.delta ≤ min 1 delta1 →
      ∃ hmem : ∀ N, MemLp (fun omega : BilateralField d =>
          affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
            (Lane4.cutoffPositiveCoefficient M H omega N 0 one_pos) u) 1 (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun N => (hmem N).toLp (fun omega : BilateralField d =>
          affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
            (Lane4.cutoffPositiveCoefficient M H omega N 0 one_pos) u)))) ∧
        ∃ B : ℝ, 0 ≤ B ∧ ∀ N, MemLp (fun omega : BilateralField d =>
            affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
              (Lane4.cutoffPositiveCoefficient M H omega N 0 one_pos) u) 2 (chaosSampleLaw M).toMeasure ∧
          eLpNorm (fun omega : BilateralField d =>
            affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
              (Lane4.cutoffPositiveCoefficient M H omega N 0 one_pos) u) 2 (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal B



theorem aux_g9_origin_entry_package_chart_eq (I : Paper.in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (K : ℕ) :
    (aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0) =
      aux_g9_sigma_entries_compact_A I M H omega K := rfl



theorem aux_g9_origin_entry_package_dirichlet
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (D : Paper.lane4_deterministic_good_scale_input d) (i j : Fin d) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
        (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
        M.delta ≤ min 1 delta1 →
        ∃ hmem : ∀ K, MemLp (fun omega => Homogenization.Book.Ch02.sigmaCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j) 1
          (chaosSampleLaw M).toMeasure,
          IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
            Homogenization.Book.Ch02.sigmaCoarse
              (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
              ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j)))) ∧
          ∃ B : ℝ, 0 ≤ B ∧ ∀ K,
            MemLp (fun omega => Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j) 2
              (chaosSampleLaw M).toMeasure ∧
            eLpNorm (fun omega => Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j) 2
              (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
  haveI hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2) := ⟨by norm_num⟩
  obtain ⟨dc, hdc, hallc⟩ := g9_sigma_entries_compact hd I Pc Xc W Sf D i j
  obtain ⟨db, hdb, hallb⟩ := g9_sigma_entries_l2_uniform hd I Pc Xc W Sf D i j
  refine ⟨min dc db, lt_min hdc hdb, ?_⟩
  intro M Rm Sreg It H hH hM
  have hMc : M.delta ≤ min 1 dc := hM.trans (min_le_min_left 1 (min_le_left _ _))
  have hMb : M.delta ≤ min 1 db := hM.trans (min_le_min_left 1 (min_le_right _ _))
  obtain ⟨hmemc, hcompactc⟩ := hallc M Rm Sreg It H hH hMc
  obtain ⟨hmemb, Bb, hBb0, hbdb⟩ := hallb M Rm Sreg It H hH hMb
  have hof2 : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  have hchart : ∀ K, (fun omega => Homogenization.Book.Ch02.sigmaCoarse
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
      ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j) =
      (fun omega => Homogenization.Book.Ch02.sigmaCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        (aux_g9_sigma_entries_compact_A I M H omega K) i j) := fun K => by
    funext omega; rw [aux_g9_origin_entry_package_chart_eq]
  have hmem1 : ∀ K, MemLp (fun omega => Homogenization.Book.Ch02.sigmaCoarse
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
      ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j) 1
      (chaosSampleLaw M).toMeasure := fun K => by rw [hchart K]; exact hmemc K
  refine ⟨hmem1, ?_, Bb, hBb0, ?_⟩
  · have hrep : (fun K => (hmem1 K).toLp (fun omega => Homogenization.Book.Ch02.sigmaCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j)) =
        (fun K => (hmemc K).toLp (fun omega => Homogenization.Book.Ch02.sigmaCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          (aux_g9_sigma_entries_compact_A I M H omega K) i j)) := by
      funext K
      exact MemLp.toLp_congr (hmem1 K) (hmemc K) (Filter.EventuallyEq.of_eq (hchart K))
    rw [hrep]; exact hcompactc
  · intro K
    have hmemb2 : MemLp (fun omega => Homogenization.Book.Ch02.sigmaCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j) 2
        (chaosSampleLaw M).toMeasure := by
      rw [hchart K, ← hof2]; exact hmemb K
    refine ⟨hmemb2, ?_⟩
    rw [hchart K, ← hof2]
    exact hbdb K



theorem aux_g9_origin_entry_package_neumann_diag
    (I : Paper.in_J d) (Cresp : ℝ)
    (hN : ∀ u : Fin d → ℝ, u ≠ 0 → aux_g9_origin_entry_package_neumannInput I Cresp u)
    (i : Fin d) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
        M.delta ≤ min 1 delta1 →
        ∃ hmem : ∀ K, MemLp (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i i) 1
          (chaosSampleLaw M).toMeasure,
          IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
            Homogenization.Book.Ch02.sigmaStarInvCoarse
              (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
              ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i i)))) ∧
          ∃ B : ℝ, 0 ≤ B ∧ ∀ K,
            MemLp (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i i) 2
              (chaosSampleLaw M).toMeasure ∧
            eLpNorm (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i i) 2
              (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
  obtain ⟨delta1, hpos, hall⟩ := hN (Pi.single i 1) (fun h => by simpa using congrFun h i)
  refine ⟨delta1, hpos, ?_⟩
  intro M Rm hRC Sreg It H hH hM
  haveI hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2) := ⟨by norm_num⟩
  obtain ⟨hmem, hcompact, B, hB0, hbd⟩ := hall M Rm hRC Sreg It H hH hM
  have hident : ∀ K, (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
      (aux_g9_sigma_entries_compact_A I M H omega K) i i) =
      (fun omega => affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
        (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1)) := fun K => by
    funext omega; exact aux_g9_sigma_entries_compact_starinv_diag I M H omega K i
  have hchart : ∀ K, (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
      ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i i) =
      (fun omega => affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
        (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1)) := fun K => by
    funext omega
    rw [aux_g9_origin_entry_package_chart_eq]
    exact congrFun (hident K) omega
  have hmem1 : ∀ K, MemLp (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
      ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i i) 1
      (chaosSampleLaw M).toMeasure := fun K => by rw [hchart K]; exact hmem K
  refine ⟨hmem1, ?_, B, hB0, ?_⟩
  · have hrep : (fun K => (hmem1 K).toLp (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i i)) =
        (fun K => (hmem K).toLp (fun omega => affineInverseNeumannResponse
          aux_lem_prefix_limit_atom_extraction_poincare.2
          (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1))) := by
      funext K
      exact MemLp.toLp_congr (hmem1 K) (hmem K) (Filter.EventuallyEq.of_eq (hchart K))
    rw [hrep]; exact hcompact
  · intro K
    rw [hchart K]; exact hbd K

/-- The `b = false` (`sigmaStarInvCoarse`, Neumann) off-diagonal (`i ≠ j`) half of the
origin-cube entry package, CONDITIONAL on `hN`: three raw-response calls to `hN` (at
`e_i+e_j`, `e_i`, `e_j`) combine into the `L¹`-compactness via `isCompact_closure_range_combo3`
and into the uniform `L²` bound via the triangle inequality, exactly mirroring
`aux_g9_sigma_entries_l2_uniform_offdiag`'s pattern but sourced from `hN` instead of
`g9_dirichlet_response_compact`. -/
theorem aux_g9_origin_entry_package_neumann_offdiag
    (I : Paper.in_J d) (Cresp : ℝ)
    (hN : ∀ u : Fin d → ℝ, u ≠ 0 → aux_g9_origin_entry_package_neumannInput I Cresp u)
    (i j : Fin d) (hij : i ≠ j) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
        M.delta ≤ min 1 delta1 →
        ∃ hmem : ∀ K, MemLp (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j) 1
          (chaosSampleLaw M).toMeasure,
          IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
            Homogenization.Book.Ch02.sigmaStarInvCoarse
              (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
              ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j)))) ∧
          ∃ B : ℝ, 0 ≤ B ∧ ∀ K,
            MemLp (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j) 2
              (chaosSampleLaw M).toMeasure ∧
            eLpNorm (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j) 2
              (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
  obtain ⟨d1, h1, hall1⟩ := hN (Pi.single i 1 + Pi.single j 1) (by
    intro h; have := congrFun h i; simp [hij.symm] at this)
  obtain ⟨d2, h2, hall2⟩ := hN (Pi.single i 1) (fun h => by simpa using congrFun h i)
  obtain ⟨d3, h3, hall3⟩ := hN (Pi.single j 1) (fun h => by simpa using congrFun h j)
  refine ⟨min d1 (min d2 d3), lt_min h1 (lt_min h2 h3), ?_⟩
  intro M Rm hRC Sreg It H hH hM
  haveI hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2) := ⟨by norm_num⟩
  have hM1 : M.delta ≤ min 1 d1 := hM.trans (min_le_min_left 1 (min_le_left _ _))
  have hM2 : M.delta ≤ min 1 d2 := hM.trans (min_le_min_left 1 ((min_le_right _ _).trans (min_le_left _ _)))
  have hM3 : M.delta ≤ min 1 d3 := hM.trans (min_le_min_left 1 ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hmemq1, hcq1, B1, hB10, hbd1⟩ := hall1 M Rm hRC Sreg It H hH hM1
  obtain ⟨hmemq2, hcq2, B2, hB20, hbd2⟩ := hall2 M Rm hRC Sreg It H hH hM2
  obtain ⟨hmemq3, hcq3, B3, hB30, hbd3⟩ := hall3 M Rm hRC Sreg It H hH hM3
  set μM := (chaosSampleLaw M).toMeasure with hμMdef
  let f1 : ℕ → BilateralField d → ℝ := fun K omega =>
    affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
      (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1 + Pi.single j 1)
  let f2 : ℕ → BilateralField d → ℝ := fun K omega =>
    affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
      (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1)
  let f3 : ℕ → BilateralField d → ℝ := fun K omega =>
    affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
      (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single j 1)
  have hchartA : ∀ K, (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
      ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j) =
      (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        (aux_g9_sigma_entries_compact_A I M H omega K) i j) := fun K => by
    funext omega; rw [aux_g9_origin_entry_package_chart_eq]
  have hident : ∀ K, (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
      (aux_g9_sigma_entries_compact_A I M H omega K) i j) =
      (fun omega => (f1 K omega - f2 K omega - f3 K omega) / 2) := fun K => by
    funext omega; exact aux_g9_sigma_entries_compact_starinv_offdiag I M H omega K i j hij
  have hdiveq : ∀ K, (fun omega => (f1 K omega - f2 K omega - f3 K omega) / 2) =
      (2⁻¹ : ℝ) • (fun omega => f1 K omega - f2 K omega - f3 K omega) := fun K => by
    funext omega; show _ = (2⁻¹ : ℝ) * _; ring
  have hcomboF : ∃ hmemF : ∀ K, MemLp (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        (aux_g9_sigma_entries_compact_A I M H omega K) i j) 1 μM,
      IsCompact (closure (Set.range (fun K => (hmemF K).toLp (fun omega =>
        Homogenization.Book.Ch02.sigmaStarInvCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          (aux_g9_sigma_entries_compact_A I M H omega K) i j)))) :=
    isCompact_closure_range_combo3 (2⁻¹ : ℝ) (-2⁻¹ : ℝ) (-2⁻¹ : ℝ)
      hmemq1 hmemq2 hmemq3 hcq1 hcq2 hcq3 (fun K => Filter.EventuallyEq.of_eq (by
        funext omega
        have hpt := congrFun (hident K) omega
        show Homogenization.Book.Ch02.sigmaStarInvCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            (aux_g9_sigma_entries_compact_A I M H omega K) i j =
          (2⁻¹ : ℝ) * f1 K omega + ((-2⁻¹ : ℝ) * f2 K omega + (-2⁻¹ : ℝ) * f3 K omega)
        rw [hpt]; ring))
  obtain ⟨hmemF, hcompactF⟩ := hcomboF
  have hmem1 : ∀ K, MemLp (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
      ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j) 1 μM :=
    fun K => by rw [hchartA K]; exact hmemF K
  refine ⟨hmem1, ?_, B1 + B2 + B3, by positivity, ?_⟩
  · have hrep : (fun K => (hmem1 K).toLp (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j)) =
        (fun K => (hmemF K).toLp (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          (aux_g9_sigma_entries_compact_A I M H omega K) i j)) := by
      funext K
      exact MemLp.toLp_congr (hmem1 K) (hmemF K) (Filter.EventuallyEq.of_eq (hchartA K))
    rw [hrep]; exact hcompactF
  · intro K
    obtain ⟨hmemb1, hbb1⟩ := hbd1 K
    obtain ⟨hmemb2, hbb2⟩ := hbd2 K
    obtain ⟨hmemb3, hbb3⟩ := hbd3 K
    have hmem2 : MemLp (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j) 2 μM := by
      rw [hchartA K, hident K, hdiveq K]
      exact (((hmemb1.sub hmemb2).sub hmemb3)).const_smul (2⁻¹ : ℝ)
    refine ⟨hmem2, ?_⟩
    rw [hchartA K, hident K, hdiveq K]
    have hsplit12 : eLpNorm (fun omega => f1 K omega - f2 K omega) 2 μM ≤
        eLpNorm (f1 K) 2 μM + eLpNorm (f2 K) 2 μM :=
      eLpNorm_sub_le (by norm_num)
    have hsplit123 : eLpNorm (fun omega => f1 K omega - f2 K omega - f3 K omega) 2 μM ≤
        eLpNorm (fun omega => f1 K omega - f2 K omega) 2 μM + eLpNorm (f3 K) 2 μM :=
      eLpNorm_sub_le (by norm_num)
    have hhalf := eLpNorm_const_smul_le_of_norm_le_one (F := ℝ)
      (c := (2⁻¹ : ℝ)) (by norm_num)
      (fun omega => f1 K omega - f2 K omega - f3 K omega) 2 μM
    calc eLpNorm ((2⁻¹ : ℝ) • (fun omega => f1 K omega - f2 K omega - f3 K omega)) 2 μM
        ≤ eLpNorm (fun omega => f1 K omega - f2 K omega - f3 K omega) 2 μM := hhalf
      _ ≤ eLpNorm (fun omega => f1 K omega - f2 K omega) 2 μM + eLpNorm (f3 K) 2 μM := hsplit123
      _ ≤ (eLpNorm (f1 K) 2 μM + eLpNorm (f2 K) 2 μM) + eLpNorm (f3 K) 2 μM := by gcongr
      _ ≤ ENNReal.ofReal B1 + ENNReal.ofReal B2 + ENNReal.ofReal B3 := by
          gcongr
      _ = ENNReal.ofReal (B1 + B2 + B3) := by
          rw [ENNReal.ofReal_add (by positivity) hB30, ENNReal.ofReal_add hB10 hB20]

/-- The full `b = false` (Neumann) half of the origin-cube entry package, CONDITIONAL on `hN`,
for any pair `(i,j)`: the diagonal and off-diagonal cases combined. -/
theorem aux_g9_origin_entry_package_neumann
    (I : Paper.in_J d) (Cresp : ℝ)
    (hN : ∀ u : Fin d → ℝ, u ≠ 0 → aux_g9_origin_entry_package_neumannInput I Cresp u)
    (i j : Fin d) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
        M.delta ≤ min 1 delta1 →
        ∃ hmem : ∀ K, MemLp (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j) 1
          (chaosSampleLaw M).toMeasure,
          IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
            Homogenization.Book.Ch02.sigmaStarInvCoarse
              (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
              ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j)))) ∧
          ∃ B : ℝ, 0 ≤ B ∧ ∀ K,
            MemLp (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j) 2
              (chaosSampleLaw M).toMeasure ∧
            eLpNorm (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j) 2
              (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
  by_cases hij : i = j
  · subst hij; exact aux_g9_origin_entry_package_neumann_diag I Cresp hN i
  · exact aux_g9_origin_entry_package_neumann_offdiag I Cresp hN i j hij



theorem g9_origin_entry_package
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (D : Paper.lane4_deterministic_good_scale_input d) (Cresp : ℝ) (hCresp : 0 < Cresp) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (b : Bool) (i j : Fin d),
        ∃ hmem : ∀ K, MemLp (fun omega => if b then
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j
            else Homogenization.Book.Ch02.sigmaStarInvCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j)
            1 (chaosSampleLaw M).toMeasure,
          IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega => if b then
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j
            else Homogenization.Book.Ch02.sigmaStarInvCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j)))) ∧
          ∃ B : ℝ, 0 ≤ B ∧ ∀ K,
            MemLp (fun omega => if b then
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j
            else Homogenization.Book.Ch02.sigmaStarInvCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j)
              2 (chaosSampleLaw M).toMeasure ∧
            eLpNorm (fun omega => if b then
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j
            else Homogenization.Book.Ch02.sigmaStarInvCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) i j)
              2 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
  have hN : ∀ u : Fin d → ℝ, u ≠ 0 → aux_g9_origin_entry_package_neumannInput I Cresp u :=
    fun u hu => g9_neumann_origin_compact d hd I Pc Xc W D Sf Cresp hCresp u hu
  have hentry : ∀ p : Bool × Fin d × Fin d,
      ∃ delta1 : ℝ, 0 < delta1 ∧
        ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
        ∀ (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M I Sreg)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
          M.delta ≤ min 1 delta1 →
          ∃ hmem : ∀ K, MemLp (fun omega => if p.1 then
                Homogenization.Book.Ch02.sigmaCoarse
                  (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                  ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) p.2.1 p.2.2
              else Homogenization.Book.Ch02.sigmaStarInvCoarse
                  (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                  ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) p.2.1 p.2.2)
              1 (chaosSampleLaw M).toMeasure,
            IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega => if p.1 then
                Homogenization.Book.Ch02.sigmaCoarse
                  (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                  ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) p.2.1 p.2.2
              else Homogenization.Book.Ch02.sigmaStarInvCoarse
                  (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                  ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) p.2.1 p.2.2)))) ∧
            ∃ B : ℝ, 0 ≤ B ∧ ∀ K,
              MemLp (fun omega => if p.1 then
                Homogenization.Book.Ch02.sigmaCoarse
                  (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                  ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) p.2.1 p.2.2
              else Homogenization.Book.Ch02.sigmaStarInvCoarse
                  (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                  ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) p.2.1 p.2.2)
                2 (chaosSampleLaw M).toMeasure ∧
              eLpNorm (fun omega => if p.1 then
                Homogenization.Book.Ch02.sigmaCoarse
                  (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                  ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) p.2.1 p.2.2
              else Homogenization.Book.Ch02.sigmaStarInvCoarse
                  (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                  ((aux_U2_unitChart I M H omega K).coeffOn (Homogenization.originCube d 0)) p.2.1 p.2.2)
                2 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
    rintro ⟨b, i, j⟩
    cases b with
    | true =>
        obtain ⟨delta1, hpos, hall⟩ := aux_g9_origin_entry_package_dirichlet hd I Pc Xc W Sf D i j
        exact ⟨delta1, hpos, fun M Rm hRC Sreg It H hH hM => by simpa using hall M Rm Sreg It H hH hM⟩
    | false =>
        obtain ⟨delta1, hpos, hall⟩ := aux_g9_origin_entry_package_neumann I Cresp hN i j
        exact ⟨delta1, hpos, fun M Rm hRC Sreg It H hH hM => by
          simpa using hall M Rm hRC Sreg It H hH hM⟩
  choose delta1 hdelta1pos hall using hentry
  have hne : (Finset.univ : Finset (Bool × Fin d × Fin d)).Nonempty := Finset.univ_nonempty
  refine ⟨min 1 (Finset.univ.inf' hne delta1), lt_min one_pos ((Finset.lt_inf'_iff hne).mpr
    (fun p _ => hdelta1pos p)), min_le_left _ _, ?_⟩
  intro M hM Rm hRC Sreg It H hH b i j
  have hMp : M.delta ≤ min 1 (delta1 (b, i, j)) := by
    refine le_min (hM.trans (min_le_left _ _)) (hM.trans ?_)
    exact (min_le_right _ _).trans (Finset.inf'_le delta1 (Finset.mem_univ (b, i, j)))
  exact hall (b, i, j) M Rm hRC Sreg It H hH hMp

end Paper
