import SubdiffusiveProcess.Paper.g9_sigma_entries_compact
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Analysis.UniformLpBound




open MeasureTheory SubdiffusiveProcess SubdiffusiveProcess.Lane4 Homogenization Set
open TopologicalSpace Homogenization.Book.Ch02
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)]

/-- Diagonal case: the `sigmaCoarse (i,i)` entry family, over the cutoff `K` at the unit root
cell, is `L²`-integrable with a single uniform norm bound `B` (no combination needed: the
`(i,i)` entry equals the raw `affineDirichletResponse` at slope `e_i` outright). -/
theorem aux_g9_sigma_entries_l2_uniform_diag
    (Jc : Paper.in_J d) (Pc : Paper.in_poincare d hd Jc) (Xc : Paper.in_extension d hd Jc)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (D : @Paper.lane4_deterministic_good_scale_input d ⟨by omega⟩) (i : Fin d) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
        (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∃ hmem2 : ∀ K, MemLp (fun omega => Book.Ch02.sigmaCoarse
            (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i i)
          (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure,
        ∃ B : ℝ, 0 ≤ B ∧ ∀ K, eLpNorm (fun omega => Book.Ch02.sigmaCoarse
            (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i i)
          (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
  obtain ⟨delta1, hdelta1, hall⟩ := g9_dirichlet_response_compact d hd Jc Pc Xc W Sf D
    (Pi.single i 1) (fun h => by simpa using congrFun h i)
  refine ⟨delta1, hdelta1, ?_⟩
  intro M Rm Sreg It H hH hM
  obtain ⟨hmem, hcompact⟩ := hall M Rm Sreg It H hH hM
  have heqfun : (fun (K : ℕ) (omega : BilateralField d) => Book.Ch02.sigmaCoarse
      (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i i) =
      (fun K omega => affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
        aux_lem_prefix_limit_atom_extraction_poincare.1
        (cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1)) := by
    funext K omega
    exact aux_g9_sigma_entries_compact_diag Jc M H omega K i
  have hmem2 : ∀ K, MemLp (fun omega => Book.Ch02.sigmaCoarse
      (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i i)
      (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure := by
    intro K
    rw [congrFun heqfun K]
    exact hmem K
  refine ⟨hmem2, ?_⟩
  obtain ⟨B, hB0, hBbd⟩ := uniform_eLpNorm_bound_of_compact_range _ hmem hcompact
  exact ⟨B, hB0, fun K => by rw [congrFun heqfun K]; exact hBbd K⟩

/-- Off-diagonal case: the `sigmaCoarse (i,j)` entry family, `i ≠ j`, over the cutoff `K` at the
unit root cell, is `L²`-integrable with a single uniform norm bound. The entry is the three-term
polarization combination `(R(e_i+e_j) - R(e_i) - R(e_j))/2` of raw `affineDirichletResponse`
values; each raw term has an `L²` bound from `g9_dirichlet_response_compact`
(`uniform_eLpNorm_bound_of_compact_range`), combined via the triangle inequality
(`eLpNorm_sub_le`) and a crude one-sided bound absorbing the `1/2` averaging factor
(`eLpNorm_const_smul_le_of_norm_le_one`). -/
theorem aux_g9_sigma_entries_l2_uniform_offdiag
    (Jc : Paper.in_J d) (Pc : Paper.in_poincare d hd Jc) (Xc : Paper.in_extension d hd Jc)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (D : @Paper.lane4_deterministic_good_scale_input d ⟨by omega⟩) (i j : Fin d) (hij : i ≠ j) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
        (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∃ hmem2 : ∀ K, MemLp (fun omega => Book.Ch02.sigmaCoarse
            (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i j)
          (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure,
        ∃ B : ℝ, 0 ≤ B ∧ ∀ K, eLpNorm (fun omega => Book.Ch02.sigmaCoarse
            (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i j)
          (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
  obtain ⟨d1, h1, hall1⟩ := g9_dirichlet_response_compact d hd Jc Pc Xc W Sf D
    (Pi.single i 1 + Pi.single j 1) (by
      intro h
      have := congrFun h i
      simp [hij.symm] at this)
  obtain ⟨d2, h2, hall2⟩ := g9_dirichlet_response_compact d hd Jc Pc Xc W Sf D
    (Pi.single i 1) (fun h => by simpa using congrFun h i)
  obtain ⟨d3, h3, hall3⟩ := g9_dirichlet_response_compact d hd Jc Pc Xc W Sf D
    (Pi.single j 1) (fun h => by simpa using congrFun h j)
  refine ⟨min d1 (min d2 d3), lt_min h1 (lt_min h2 h3), ?_⟩
  intro M Rm Sreg It H hH hM
  have hM1 : M.delta ≤ min 1 d1 := hM.trans (min_le_min_left 1 (min_le_left _ _))
  have hM2 : M.delta ≤ min 1 d2 := hM.trans (min_le_min_left 1 ((min_le_right _ _).trans (min_le_left _ _)))
  have hM3 : M.delta ≤ min 1 d3 := hM.trans (min_le_min_left 1 ((min_le_right _ _).trans (min_le_right _ _)))
  let μM := (chaosSampleLaw M).toMeasure
  let f1 : ℕ → BilateralField d → ℝ := fun K omega =>
      affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
        aux_lem_prefix_limit_atom_extraction_poincare.1
        (cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1 + Pi.single j 1)
  let f2 : ℕ → BilateralField d → ℝ := fun K omega =>
      affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
        aux_lem_prefix_limit_atom_extraction_poincare.1
        (cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1)
  let f3 : ℕ → BilateralField d → ℝ := fun K omega =>
      affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
        aux_lem_prefix_limit_atom_extraction_poincare.1
        (cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single j 1)
  obtain ⟨hmemq1, hcq1⟩ := hall1 M Rm Sreg It H hH hM1
  obtain ⟨hmemq2, hcq2⟩ := hall2 M Rm Sreg It H hH hM2
  obtain ⟨hmemq3, hcq3⟩ := hall3 M Rm Sreg It H hH hM3
  obtain ⟨B1, hB10, hB1bd⟩ := uniform_eLpNorm_bound_of_compact_range f1 hmemq1 hcq1
  obtain ⟨B2, hB20, hB2bd⟩ := uniform_eLpNorm_bound_of_compact_range f2 hmemq2 hcq2
  obtain ⟨B3, hB30, hB3bd⟩ := uniform_eLpNorm_bound_of_compact_range f3 hmemq3 hcq3
  have heqfun : ∀ K, (fun omega => Book.Ch02.sigmaCoarse
      (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i j) =
      (fun omega => (f1 K omega - f2 K omega - f3 K omega) / 2) := by
    intro K
    funext omega
    exact aux_g9_sigma_entries_compact_offdiag Jc M H omega K i j hij
  have hdiveq : ∀ K, (fun omega => (f1 K omega - f2 K omega - f3 K omega) / 2) =
      (2⁻¹ : ℝ) • (fun omega => f1 K omega - f2 K omega - f3 K omega) := fun K => by
    funext omega
    show _ = (2⁻¹ : ℝ) * _
    ring
  have hmem2 : ∀ K, MemLp (fun omega => Book.Ch02.sigmaCoarse
      (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i j)
      (ENNReal.ofReal 2) μM := by
    intro K
    rw [heqfun K, hdiveq K]
    exact ((hmemq1 K).sub (hmemq2 K)).sub (hmemq3 K) |>.const_smul (2⁻¹ : ℝ)
  refine ⟨hmem2, B1 + B2 + B3, by positivity, fun K => ?_⟩
  rw [heqfun K, hdiveq K]
  have hsplit12 : eLpNorm (fun omega => f1 K omega - f2 K omega) (ENNReal.ofReal 2) μM ≤
      eLpNorm (f1 K) (ENNReal.ofReal 2) μM + eLpNorm (f2 K) (ENNReal.ofReal 2) μM :=
    eLpNorm_sub_le (hmemq1 K).1 (hmemq2 K).1 hp2.out
  have hsplit123 : eLpNorm (fun omega => f1 K omega - f2 K omega - f3 K omega) (ENNReal.ofReal 2) μM ≤
      eLpNorm (fun omega => f1 K omega - f2 K omega) (ENNReal.ofReal 2) μM +
      eLpNorm (f3 K) (ENNReal.ofReal 2) μM :=
    eLpNorm_sub_le ((hmemq1 K).sub (hmemq2 K)).1 (hmemq3 K).1 hp2.out
  have hhalf := eLpNorm_const_smul_le_of_norm_le_one (F := ℝ)
    (c := (2⁻¹ : ℝ)) (by norm_num)
    (fun omega => f1 K omega - f2 K omega - f3 K omega) (ENNReal.ofReal 2) μM
  calc eLpNorm ((2⁻¹ : ℝ) • (fun omega => f1 K omega - f2 K omega - f3 K omega)) (ENNReal.ofReal 2) μM
      ≤ eLpNorm (fun omega => f1 K omega - f2 K omega - f3 K omega) (ENNReal.ofReal 2) μM := hhalf
    _ ≤ eLpNorm (fun omega => f1 K omega - f2 K omega) (ENNReal.ofReal 2) μM +
        eLpNorm (f3 K) (ENNReal.ofReal 2) μM := hsplit123
    _ ≤ (eLpNorm (f1 K) (ENNReal.ofReal 2) μM + eLpNorm (f2 K) (ENNReal.ofReal 2) μM) +
        eLpNorm (f3 K) (ENNReal.ofReal 2) μM := by gcongr
    _ ≤ ENNReal.ofReal B1 + ENNReal.ofReal B2 + ENNReal.ofReal B3 := by
        gcongr
        · exact hB1bd K
        · exact hB2bd K
        · exact hB3bd K
    _ = ENNReal.ofReal (B1 + B2 + B3) := by
        rw [ENNReal.ofReal_add (by positivity) hB30, ENNReal.ofReal_add hB10 hB20]

/-- The `sigmaCoarse` entry family (at the unit root cell, for any pair of directions `(i,j)`)
is `L²`-integrable with a single uniform-in-`K` norm bound, feeding the general-`R` lift's
random-multiplier compactness transport (`isCompact_closure_range_smul_of_memLp_higher`). -/
theorem g9_sigma_entries_l2_uniform
    (Jc : Paper.in_J d) (Pc : Paper.in_poincare d hd Jc) (Xc : Paper.in_extension d hd Jc)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (D : @Paper.lane4_deterministic_good_scale_input d ⟨by omega⟩) (i j : Fin d) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
        (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∃ hmem2 : ∀ K, MemLp (fun omega => Book.Ch02.sigmaCoarse
            (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i j)
          (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure,
        ∃ B : ℝ, 0 ≤ B ∧ ∀ K, eLpNorm (fun omega => Book.Ch02.sigmaCoarse
            (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i j)
          (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
  by_cases hij : i = j
  · subst hij
    exact aux_g9_sigma_entries_l2_uniform_diag hd Jc Pc Xc W Sf D i
  · exact aux_g9_sigma_entries_l2_uniform_offdiag hd Jc Pc Xc W Sf D i j hij

end Paper
