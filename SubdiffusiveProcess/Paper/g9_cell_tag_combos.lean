module

public import SubdiffusiveProcess.Paper.g9_cell_entry_memLp
public import SubdiffusiveProcess.Paper.g9_general_R_entry_lift
public import SubdiffusiveProcess.Paper.g9_matrixnorm_entries_compact
public import SubdiffusiveProcess.Paper.g9_probemax_entries_compact
public import SubdiffusiveProcess.Paper.probemax_measurable_R_gen
public import SubdiffusiveProcess.Analysis.LipschitzLpCompact

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Input interface for `SubdiffusiveProcess.Paper.g9_origin_entry_package`, carried as an explicit hypothesis. -/
def aux_g9_cell_tag_combos_originPackageType {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I) (_Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (_Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_D : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d) (Cresp : ℝ) (_hCresp : 0 < Cresp) : Prop :=
  ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
    ∀ (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M), Rm.C ≤ Cresp →
    ∀ (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
    ∀ (b : Bool) (i j : Fin d),
      ∃ hmem : ∀ K, MemLp (g9_cell_entry I M H (Homogenization.originCube d 0) b i j K) 1
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp
            (g9_cell_entry I M H (Homogenization.originCube d 0) b i j K)))) ∧
        ∃ B : ℝ, 0 ≤ B ∧ ∀ K,
          MemLp (g9_cell_entry I M H (Homogenization.originCube d 0) b i j K) 2
            (chaosSampleLaw M).toMeasure ∧
          eLpNorm (g9_cell_entry I M H (Homogenization.originCube d 0) b i j K) 2
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B

/-- General-cell entry compactness (`b i j` fixed, `R` general): combines the origin package
with `g9_cell_entry_memLp` (`hRmem`) via `g9_general_R_entry_lift`. -/
theorem aux_g9_cell_tag_combos_entry_at_R {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (D : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d) (Cresp : ℝ) (hCresp : 0 < Cresp)
    (hOrigin : aux_g9_cell_tag_combos_originPackageType hd I Pc Xc W Sf D Cresp hCresp) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (R : Homogenization.TriadicCube d),
        Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) →
      ∀ (b : Bool) (i j : Fin d),
        ∃ hmem : ∀ K, MemLp (g9_cell_entry I M H R b i j K) 1 (chaosSampleLaw M).toMeasure,
          IsCompact (closure (Set.range (fun K => (hmem K).toLp (g9_cell_entry I M H R b i j K)))) := by
  obtain ⟨delta0o, hdelta0o, hdelta0ole, hOriginM⟩ := hOrigin
  obtain ⟨delta0m, hdelta0m, hMemLp⟩ :=
    g9_cell_entry_memLp hd I Pc Xc W Sf D Cresp hCresp
  refine ⟨min delta0o delta0m, lt_min hdelta0o hdelta0m, ?_⟩
  intro M hM Rm hRm Sreg It H hH R hR b i j
  have hMo : M.delta ≤ delta0o := hM.trans (min_le_left _ _)
  have hMm : M.delta ≤ delta0m := hM.trans (min_le_right _ _)
  obtain ⟨h0mem, h0cpt, B, hBnonneg, h0L2⟩ := hOriginM M hMo Rm hRm Sreg It H hH b i j
  have hRmem := hMemLp M hMm Rm hRm Sreg It H hH R hR b i j
  refine ⟨hRmem, ?_⟩
  exact g9_general_R_entry_lift hd I M Rm H hH delta0o hdelta0o hdelta0ole hMo R hR b i j
    h0mem h0cpt B h0L2 hRmem

/-- Combine `sigma`-entry compactness at `R` (all `d²` entries) into `coarseBMatrixNorm R`
compactness, general in `R`. -/
theorem aux_g9_cell_tag_combos_B_at_R {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0))
    (hall : ∀ p : Fin d × Fin d,
      ∃ hmem : ∀ K, MemLp (g9_cell_entry I M H R true p.1 p.2 K) 1 (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (g9_cell_entry I M H R true p.1 p.2 K))))) :
    ∃ hmem : ∀ K, MemLp (fun omega => Book.Ch02.coarseBMatrixNorm R (aux_U2_unitChart I M H omega K)) 1
        (chaosSampleLaw M).toMeasure,
      IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
        Book.Ch02.coarseBMatrixNorm R (aux_U2_unitChart I M H omega K))))) := by
  choose hmemEntry hcompactEntry using hall
  set f2 : Fin d × Fin d → ℕ → BilateralField d → ℝ := fun p K omega =>
    g9_cell_entry I M H R true p.1 p.2 K omega with hf2def
  obtain ⟨hcombMem, hcombCompact⟩ := isCompact_closure_range_lipschitz_combo
    (f := f2) (hmem := hmemEntry) (hf := hcompactEntry)
    (g := aux_g9_matrixnorm_entries_compact_g d) (c := (Fintype.card (Fin d) : ℝ))
    (hc := by positivity) (hg0 := aux_g9_matrixnorm_entries_compact_g0)
    (hglip := aux_g9_matrixnorm_entries_compact_glip)
  have heqfun : (fun (K : ℕ) (omega : BilateralField d) =>
      Book.Ch02.coarseBMatrixNorm R (aux_U2_unitChart I M H omega K)) =
      (fun K omega => aux_g9_matrixnorm_entries_compact_g d (fun p => f2 p K omega)) := by
    funext K omega
    show Book.Ch02.coarseBMatrixNorm R (aux_U2_unitChart I M H omega K) = _
    unfold aux_U2_unitChart
    unfold Book.Ch02.coarseBMatrixNorm aux_g9_matrixnorm_entries_compact_g
    have heq := aux_core_sigmaCoarse_eq_bCoarse_R hd I 0 1 one_pos
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega K 0 one_pos) R hR
    rw [← heq]
    rfl
  have hmem1 : ∀ K, MemLp (fun omega =>
      Book.Ch02.coarseBMatrixNorm R (aux_U2_unitChart I M H omega K)) 1
      (chaosSampleLaw M).toMeasure := by
    intro K
    rw [show (fun omega => Book.Ch02.coarseBMatrixNorm R (aux_U2_unitChart I M H omega K)) =
        (fun omega => aux_g9_matrixnorm_entries_compact_g d (fun p => f2 p K omega)) from
      congrFun heqfun K]
    exact hcombMem K
  refine ⟨hmem1, ?_⟩
  have hrep : (fun K => (hmem1 K).toLp (fun omega =>
      Book.Ch02.coarseBMatrixNorm R (aux_U2_unitChart I M H omega K))) =
      (fun K => (hcombMem K).toLp (fun omega => aux_g9_matrixnorm_entries_compact_g d
        (fun p => f2 p K omega))) := by
    funext K
    exact MemLp.toLp_congr (hmem1 K) (hcombMem K) (Filter.EventuallyEq.of_eq (congrFun heqfun K))
  rw [hrep]
  exact hcombCompact

/-- Combine `sigma_*^{-1}`-entry compactness at `R` (all `d²` entries) into
`coarseSigmaStarInvMatrixNorm R` compactness, general in `R`. -/
theorem aux_g9_cell_tag_combos_SigmaStarInv_at_R {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (R : Homogenization.TriadicCube d)
    (hall : ∀ p : Fin d × Fin d,
      ∃ hmem : ∀ K, MemLp (g9_cell_entry I M H R false p.1 p.2 K) 1 (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (g9_cell_entry I M H R false p.1 p.2 K))))) :
    ∃ hmem : ∀ K, MemLp (fun omega =>
        Book.Ch02.coarseSigmaStarInvMatrixNorm R (aux_U2_unitChart I M H omega K)) 1
        (chaosSampleLaw M).toMeasure,
      IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
        Book.Ch02.coarseSigmaStarInvMatrixNorm R (aux_U2_unitChart I M H omega K))))) := by
  choose hmemEntry hcompactEntry using hall
  set f2 : Fin d × Fin d → ℕ → BilateralField d → ℝ := fun p K omega =>
    g9_cell_entry I M H R false p.1 p.2 K omega with hf2def
  obtain ⟨hcombMem, hcombCompact⟩ := isCompact_closure_range_lipschitz_combo
    (f := f2) (hmem := hmemEntry) (hf := hcompactEntry)
    (g := aux_g9_matrixnorm_entries_compact_g d) (c := (Fintype.card (Fin d) : ℝ))
    (hc := by positivity) (hg0 := aux_g9_matrixnorm_entries_compact_g0)
    (hglip := aux_g9_matrixnorm_entries_compact_glip)
  have heqfun : (fun (K : ℕ) (omega : BilateralField d) =>
      Book.Ch02.coarseSigmaStarInvMatrixNorm R (aux_U2_unitChart I M H omega K)) =
      (fun K omega => aux_g9_matrixnorm_entries_compact_g d (fun p => f2 p K omega)) := by
    funext K omega
    show Book.Ch02.coarseSigmaStarInvMatrixNorm R (aux_U2_unitChart I M H omega K) = _
    unfold aux_U2_unitChart
    unfold Book.Ch02.coarseSigmaStarInvMatrixNorm aux_g9_matrixnorm_entries_compact_g
    rfl
  have hmem1 : ∀ K, MemLp (fun omega =>
      Book.Ch02.coarseSigmaStarInvMatrixNorm R (aux_U2_unitChart I M H omega K)) 1
      (chaosSampleLaw M).toMeasure := by
    intro K
    rw [show (fun omega => Book.Ch02.coarseSigmaStarInvMatrixNorm R (aux_U2_unitChart I M H omega K)) =
        (fun omega => aux_g9_matrixnorm_entries_compact_g d (fun p => f2 p K omega)) from
      congrFun heqfun K]
    exact hcombMem K
  refine ⟨hmem1, ?_⟩
  have hrep : (fun K => (hmem1 K).toLp (fun omega =>
      Book.Ch02.coarseSigmaStarInvMatrixNorm R (aux_U2_unitChart I M H omega K))) =
      (fun K => (hcombMem K).toLp (fun omega => aux_g9_matrixnorm_entries_compact_g d
        (fun p => f2 p K omega))) := by
    funext K
    exact MemLp.toLp_congr (hmem1 K) (hcombMem K) (Filter.EventuallyEq.of_eq (congrFun heqfun K))
  rw [hrep]
  exact hcombCompact

/-- Compactness of the `(sigma, sigmaStarInv, identity)` triple at `R`, index `p`, given entry
compactness at `R` for both `b = true/false`. The `k = 2` (identity) branch is `omega`-independent
(constant), hence trivially `MemLp` and compact. -/
theorem aux_g9_cell_tag_combos_triple_at_R {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (R : Homogenization.TriadicCube d)
    (hentry : ∀ (b : Bool) (i j : Fin d),
      ∃ hmem : ∀ K, MemLp (g9_cell_entry I M H R b i j K) 1 (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (g9_cell_entry I M H R b i j K)))))
    (p : Fin d × Fin d × Fin 3) :
    ∃ hmem : ∀ K, MemLp (fun omega => aux_probemax_measurable_R_gen_triple I M H R p K omega) 1
        (chaosSampleLaw M).toMeasure,
      IsCompact (closure (Set.range (fun K => (hmem K).toLp
        (fun omega => aux_probemax_measurable_R_gen_triple I M H R p K omega)))) := by
  obtain ⟨i, j, k⟩ := p
  by_cases hk0 : k = 0
  · subst hk0
    exact hentry true i j
  · by_cases hk1 : k = 1
    · subst hk1
      exact hentry false i j
    · have hk2 : k = 2 := by omega
      subst hk2
      have h20 : ¬ (2 : Fin 3) = 0 := by decide
      have h21 : ¬ (2 : Fin 3) = 1 := by decide
      have hconstfun : ∀ K, (fun omega => aux_probemax_measurable_R_gen_triple I M H R (i, j, 2) K omega) =
          (fun _ : BilateralField d => if i = j then (1 : ℝ) else (0 : ℝ)) := by
        intro K
        funext omega
        show (if (2 : Fin 3) = 0 then _ else if (2 : Fin 3) = 1 then _ else _) = _
        rw [ite_eq_right h20, ite_eq_right h21]
      have hmemc : ∀ K, MemLp (fun omega => aux_probemax_measurable_R_gen_triple I M H R (i, j, 2) K omega) 1
          (chaosSampleLaw M).toMeasure := by
        intro K; rw [hconstfun K]; exact memLp_const _
      refine ⟨hmemc, ?_⟩
      have hrep : (fun K => (hmemc K).toLp
          (fun omega => aux_probemax_measurable_R_gen_triple I M H R (i, j, 2) K omega)) =
          (fun _ : ℕ => (memLp_const (μ := (chaosSampleLaw M).toMeasure)
            (if i = j then (1 : ℝ) else (0 : ℝ))).toLp
            (fun _ : BilateralField d => if i = j then (1 : ℝ) else (0 : ℝ))) := by
        funext K
        exact MemLp.toLp_congr (hmemc K) (memLp_const _) (Filter.EventuallyEq.of_eq (hconstfun K))
      rw [hrep, Set.range_const, closure_singleton]
      exact isCompact_singleton

/-- Combine the `(sigma, sigmaStarInv, identity)` triple compactness at `R` into
`paperScalarProbeMax R F 1` compactness, general in `R`. -/
theorem aux_g9_cell_tag_combos_probeMax_at_R {d : ℕ} (_hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0))
    (hentry : ∀ (b : Bool) (i j : Fin d),
      ∃ hmem : ∀ K, MemLp (g9_cell_entry I M H R b i j K) 1 (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (g9_cell_entry I M H R b i j K))))) :
    ∃ hmem : ∀ K, MemLp (fun omega =>
        (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (aux_U2_unitChart I M H omega K) 1).toReal) 1
        (chaosSampleLaw M).toMeasure,
      IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
        (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (aux_U2_unitChart I M H omega K) 1).toReal)))) := by
  have hall := fun p => aux_g9_cell_tag_combos_triple_at_R I M H R hentry p
  choose hmemEntry hcompactEntry using hall
  set f2 : (Fin d × Fin d × Fin 3) → ℕ → BilateralField d → ℝ := fun p K omega =>
    aux_probemax_measurable_R_gen_triple I M H R p K omega with hf2def
  obtain ⟨hcombMem, hcombCompact⟩ := isCompact_closure_range_lipschitz_combo
    (f := f2) (hmem := hmemEntry) (hf := hcompactEntry)
    (g := aux_g9_probemax_entries_compact_g d) (c := (Fintype.card (Fin d) : ℝ))
    (hc := by positivity) (hg0 := aux_g9_probemax_entries_compact_g0 d)
    (hglip := aux_g9_probemax_entries_compact_glip d)
  have heqfun : (fun (K : ℕ) (omega : BilateralField d) =>
      (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (aux_U2_unitChart I M H omega K) 1).toReal) =
      (fun K omega => aux_g9_probemax_entries_compact_g d (fun p => f2 p K omega)) := by
    funext K omega
    show (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
        (I.chart 0 1 one_pos (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1) 1).toReal = _
    exact aux_probemax_measurable_R_gen_triple_eq I M H omega K R hR
  have hmem1 : ∀ K, MemLp (fun omega =>
      (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (aux_U2_unitChart I M H omega K) 1).toReal) 1
      (chaosSampleLaw M).toMeasure := by
    intro K
    rw [show (fun omega => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
        (aux_U2_unitChart I M H omega K) 1).toReal) =
        (fun omega => aux_g9_probemax_entries_compact_g d (fun p => f2 p K omega)) from
      congrFun heqfun K]
    exact hcombMem K
  refine ⟨hmem1, ?_⟩
  have hrep : (fun K => (hmem1 K).toLp (fun omega =>
      (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (aux_U2_unitChart I M H omega K) 1).toReal)) =
      (fun K => (hcombMem K).toLp (fun omega => aux_g9_probemax_entries_compact_g d
        (fun p => f2 p K omega))) := by
    funext K
    exact MemLp.toLp_congr (hmem1 K) (hcombMem K) (Filter.EventuallyEq.of_eq (congrFun heqfun K))
  rw [hrep]
  exact hcombCompact

/-- Full cell-compactness, all five tags, general in `R`, conditional on the origin-cube entry
package (`hOrigin`, typed exactly as `SubdiffusiveProcess.Paper.g9_origin_entry_package`'s conclusion). -/
theorem g9_cell_tag_combos {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (D : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d) (Cresp : ℝ) (hCresp : 0 < Cresp)
    (hOrigin : aux_g9_cell_tag_combos_originPackageType hd I Pc Xc W Sf D Cresp hCresp) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (R : Homogenization.TriadicCube d),
        Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) →
      (∀ (b : Bool) (i j : Fin d),
        ∃ hmem : ∀ K, MemLp (g9_cell_entry I M H R b i j K) 1 (chaosSampleLaw M).toMeasure,
          IsCompact (closure (Set.range (fun K => (hmem K).toLp (g9_cell_entry I M H R b i j K))))) ∧
      (∃ hmem : ∀ K, MemLp (fun omega => Book.Ch02.coarseBMatrixNorm R (aux_U2_unitChart I M H omega K)) 1
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
          Book.Ch02.coarseBMatrixNorm R (aux_U2_unitChart I M H omega K)))))) ∧
      (∃ hmem : ∀ K, MemLp (fun omega =>
          Book.Ch02.coarseSigmaStarInvMatrixNorm R (aux_U2_unitChart I M H omega K)) 1
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
          Book.Ch02.coarseSigmaStarInvMatrixNorm R (aux_U2_unitChart I M H omega K)))))) ∧
      (∃ hmem : ∀ K, MemLp (fun omega =>
          (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (aux_U2_unitChart I M H omega K) 1).toReal) 1
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
          (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (aux_U2_unitChart I M H omega K) 1).toReal)))))
      := by
  obtain ⟨delta0, hdelta0, hall⟩ :=
    aux_g9_cell_tag_combos_entry_at_R hd I Pc Xc W Sf D Cresp hCresp hOrigin
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hM Rm hRm Sreg It H hH R hR
  have hentry : ∀ (b : Bool) (i j : Fin d),
      ∃ hmem : ∀ K, MemLp (g9_cell_entry I M H R b i j K) 1 (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (g9_cell_entry I M H R b i j K)))) :=
    fun b i j => hall M hM Rm hRm Sreg It H hH R hR b i j
  refine ⟨hentry, ?_, ?_, ?_⟩
  · exact aux_g9_cell_tag_combos_B_at_R hd I M H R hR (fun p => hentry true p.1 p.2)
  · exact aux_g9_cell_tag_combos_SigmaStarInv_at_R I M H R (fun p => hentry false p.1 p.2)
  · exact aux_g9_cell_tag_combos_probeMax_at_R hd I M H R hR hentry

end SubdiffusiveProcess.Paper
