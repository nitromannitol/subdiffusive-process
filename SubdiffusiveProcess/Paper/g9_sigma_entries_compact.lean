import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_chart_response_transfer
import SubdiffusiveProcess.Paper.lem_extension_cell_moment
import SubdiffusiveProcess.Paper.g9_dirichlet_response_compact
import SubdiffusiveProcess.Paper.NeumannResponseCompactAtOrigin
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import Homogenization.Book.Ch02.Theorems.MatrixExtractionProofs
import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
import SubdiffusiveProcess.Analysis.LpExponentCompact

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

theorem aux_bridge1_scalar_ae (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (K : ℕ) :
    ((I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1).coeffOn
        (Homogenization.originCube d 0)).toCoeffField
      =ᵐ[volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d 0))]
      fun x => Homogenization.scalarMatrix (cutoffCoefficient M H omega K x) := by
  have h := aux_lem_extension_cell_moment_chart_scalar_identity I M H omega K
    (0 : SpatialCoordinates d) 1 one_pos (0 : SpatialCoordinates d) 1 one_pos subset_rfl
    (Homogenization.originCube d 0) subset_rfl
  filter_upwards [h] with x hx
  have hfeq : (fun i => (0 : SpatialCoordinates d) i + 1 * x i) = x := by funext i; simp
  rw [hx, hfeq]

theorem aux_bridge1_dirichletNu_eq (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (K : ℕ)
    (p : Fin d → ℝ) :
    symmetricDirichletNu (cubeDomain (Homogenization.originCube d 0))
      ((I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1).coeffOn
        (Homogenization.originCube d 0)) p =
      affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
        aux_lem_prefix_limit_atom_extraction_poincare.1
        (cutoffPositiveCoefficient M H omega K 0 one_pos) p / 2 :=
  (aux_chart_transfer_scalar_nu
    ((I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1).coeffOn
      (Homogenization.originCube d 0))
    (cutoffCoefficient M H omega K) (cutoffCoefficient_continuous M H omega K)
    (cutoffCoefficient_pos M H omega K) (aux_bridge1_scalar_ae I M H omega K) p).1



theorem aux_bridge1_neumannNu_eq (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (K : ℕ)
    (p : Fin d → ℝ) :
    symmetricNeumannNu (cubeDomain (Homogenization.originCube d 0))
      ((I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1).coeffOn
        (Homogenization.originCube d 0)) p =
      affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
        (cutoffPositiveCoefficient M H omega K 0 one_pos) p / 2 :=
  (aux_chart_transfer_scalar_nu
    ((I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1).coeffOn
      (Homogenization.originCube d 0))
    (cutoffCoefficient M H omega K) (cutoffCoefficient_continuous M H omega K)
    (cutoffCoefficient_pos M H omega K) (aux_bridge1_scalar_ae I M H omega K) p).2

/-- The chart coefficient family on the origin cube, at a fixed cutoff `K`. -/
abbrev aux_g9_sigma_entries_compact_A (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (K : ℕ) :
    CoeffOn (cubeDomain (Homogenization.originCube d 0)) :=
  (I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1).coeffOn
    (Homogenization.originCube d 0)

theorem aux_g9_sigma_entries_compact_canonicalSigma_eq_symmDirichletNu {d : ℕ}
    (U : Domain d) (A : CoeffOn U) (hsym : CoeffOn.IsSymmetric A) (p : Vec d) :
    canonicalSigmaCorrectedResponse U A p = symmetricDirichletNu U A p := by
  have h1 := canonicalSigmaCorrectedResponse_eq_sigmaCoarse U A p
  have h2 := (responseSymmetricDirichletNeumannTheory U A hsym).dirichlet_value_by_sigma p
  rw [h1, h2]

/-- `responseJ U A 0 q` is exactly `symmetricNeumannNu U A q` for symmetric `A`: the Dirichlet
term of the `response_dirichlet_neumann_split` vanishes at `p = 0` since `dirichlet_value_by_sigma`
gives `symmetricDirichletNu U A 0 = (1/2)*0·sigmaCoarse·0 = 0`. -/
theorem aux_g9_sigma_entries_compact_responseJ_zero_eq_symmNeumannNu {d : ℕ}
    (U : Domain d) (A : CoeffOn U) (hsym : CoeffOn.IsSymmetric A) (q : Vec d) :
    responseJ U A 0 q = symmetricNeumannNu U A q := by
  have hthy := responseSymmetricDirichletNeumannTheory U A hsym
  have hsplit := hthy.response_dirichlet_neumann_split 0 q
  have hzero : symmetricDirichletNu U A 0 = 0 := by
    rw [hthy.dirichlet_value_by_sigma]
    simp [vecDot, matVecMul]
  rw [hsplit, hzero]
  simp [vecDot]

theorem aux_g9_sigma_entries_compact_symm (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (K : ℕ) :
    CoeffOn.IsSymmetric (aux_g9_sigma_entries_compact_A I M H omega K) := by
  filter_upwards [aux_bridge1_scalar_ae I M H omega K] with x hx
  unfold aux_g9_sigma_entries_compact_A
  rw [hx]
  exact Homogenization.scalarMatrix_isSymm _

/-- `sigmaCoarse` entry `(i,i)` of the identity chart on the origin cube equals the actual
`affineDirichletResponse` at slope `e_i` (no `1/2` correction: `2 * (·/2) = ·`). -/
theorem aux_g9_sigma_entries_compact_diag (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (K : ℕ)
    (i : Fin d) :
    Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A I M H omega K) i i =
      affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
        aux_lem_prefix_limit_atom_extraction_poincare.1
        (cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1) := by
  have h1 : Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A I M H omega K) i i
      = sigmaEntry (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A I M H omega K) i i := rfl
  have e1 := aux_g9_sigma_entries_compact_canonicalSigma_eq_symmDirichletNu
    (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A I M H omega K)
    (aux_g9_sigma_entries_compact_symm I M H omega K) (Pi.single i 1)
  have b1 := aux_bridge1_dirichletNu_eq I M H omega K (Pi.single i (1 : ℝ))
  rw [h1]
  unfold sigmaEntry
  rw [dif_pos rfl]
  linarith [e1, b1]

/-- `sigmaCoarse` off-diagonal entry `(i,j)`, `i ≠ j`, of the identity chart on the origin cube. -/
theorem aux_g9_sigma_entries_compact_offdiag (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (K : ℕ)
    (i j : Fin d) (hij : i ≠ j) :
    Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A I M H omega K) i j =
      (affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
          aux_lem_prefix_limit_atom_extraction_poincare.1
          (cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1 + Pi.single j 1)
        - affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
          aux_lem_prefix_limit_atom_extraction_poincare.1
          (cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1)
        - affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
          aux_lem_prefix_limit_atom_extraction_poincare.1
          (cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single j 1)) / 2 := by
  have h1 : Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A I M H omega K) i j
      = sigmaEntry (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A I M H omega K) i j := rfl
  have e1 := aux_g9_sigma_entries_compact_canonicalSigma_eq_symmDirichletNu
    (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A I M H omega K)
    (aux_g9_sigma_entries_compact_symm I M H omega K) (Pi.single i 1 + Pi.single j 1)
  have e2 := aux_g9_sigma_entries_compact_canonicalSigma_eq_symmDirichletNu
    (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A I M H omega K)
    (aux_g9_sigma_entries_compact_symm I M H omega K) (Pi.single i (1 : ℝ))
  have e3 := aux_g9_sigma_entries_compact_canonicalSigma_eq_symmDirichletNu
    (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A I M H omega K)
    (aux_g9_sigma_entries_compact_symm I M H omega K) (Pi.single j (1 : ℝ))
  have b1 := aux_bridge1_dirichletNu_eq I M H omega K (Pi.single i 1 + Pi.single j 1)
  have b2 := aux_bridge1_dirichletNu_eq I M H omega K (Pi.single i (1 : ℝ))
  have b3 := aux_bridge1_dirichletNu_eq I M H omega K (Pi.single j (1 : ℝ))
  rw [h1]
  unfold sigmaEntry
  rw [dif_neg hij]
  linarith [e1, e2, e3, b1, b2, b3]

/-- `sigmaStarInvCoarse` entry `(i,i)`, the Neumann mirror of `aux_g9_sigma_entries_compact_diag`. -/
theorem aux_g9_sigma_entries_compact_starinv_diag (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (K : ℕ)
    (i : Fin d) :
    Book.Ch02.sigmaStarInvCoarse (cubeDomain (Homogenization.originCube d 0))
        (aux_g9_sigma_entries_compact_A I M H omega K) i i =
      affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
        (cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1) := by
  have h1 : Book.Ch02.sigmaStarInvCoarse (cubeDomain (Homogenization.originCube d 0))
      (aux_g9_sigma_entries_compact_A I M H omega K) i i
      = sigmaStarInvEntry (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A I M H omega K) i i := rfl
  have e1 := aux_g9_sigma_entries_compact_responseJ_zero_eq_symmNeumannNu
    (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A I M H omega K)
    (aux_g9_sigma_entries_compact_symm I M H omega K) (Pi.single i 1)
  have b1 := aux_bridge1_neumannNu_eq I M H omega K (Pi.single i (1 : ℝ))
  rw [h1]
  unfold sigmaStarInvEntry
  rw [dif_pos rfl]
  linarith [e1, b1]

/-- `sigmaStarInvCoarse` off-diagonal entry `(i,j)`, `i ≠ j`, the Neumann mirror of
`aux_g9_sigma_entries_compact_offdiag`. -/
theorem aux_g9_sigma_entries_compact_starinv_offdiag (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (K : ℕ)
    (i j : Fin d) (hij : i ≠ j) :
    Book.Ch02.sigmaStarInvCoarse (cubeDomain (Homogenization.originCube d 0))
        (aux_g9_sigma_entries_compact_A I M H omega K) i j =
      (affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
          (cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1 + Pi.single j 1)
        - affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
          (cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1)
        - affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
          (cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single j 1)) / 2 := by
  have h1 : Book.Ch02.sigmaStarInvCoarse (cubeDomain (Homogenization.originCube d 0))
      (aux_g9_sigma_entries_compact_A I M H omega K) i j
      = sigmaStarInvEntry (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A I M H omega K) i j := rfl
  have e1 := aux_g9_sigma_entries_compact_responseJ_zero_eq_symmNeumannNu
    (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A I M H omega K)
    (aux_g9_sigma_entries_compact_symm I M H omega K) (Pi.single i 1 + Pi.single j 1)
  have e2 := aux_g9_sigma_entries_compact_responseJ_zero_eq_symmNeumannNu
    (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A I M H omega K)
    (aux_g9_sigma_entries_compact_symm I M H omega K) (Pi.single i (1 : ℝ))
  have e3 := aux_g9_sigma_entries_compact_responseJ_zero_eq_symmNeumannNu
    (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A I M H omega K)
    (aux_g9_sigma_entries_compact_symm I M H omega K) (Pi.single j (1 : ℝ))
  have b1 := aux_bridge1_neumannNu_eq I M H omega K (Pi.single i 1 + Pi.single j 1)
  have b2 := aux_bridge1_neumannNu_eq I M H omega K (Pi.single i (1 : ℝ))
  have b3 := aux_bridge1_neumannNu_eq I M H omega K (Pi.single j (1 : ℝ))
  rw [h1]
  unfold sigmaStarInvEntry
  rw [dif_neg hij]
  linarith [e1, e2, e3, b1, b2, b3]

/-- Diagonal case compactness: `sigmaCoarse (i,i)` is, as a family over the cutoff `K`,
integrable and relatively compact in `L¹`, for any model below the threshold `g9_dirichlet_response_compact`
supplies (no `Cresp` bound needed: this holds uniformly in `Rm`). -/
theorem aux_g9_sigma_entries_compact_diag_compact
    (Jc : Paper.in_J d) (Pc : Paper.in_poincare d hd Jc) (Xc : Paper.in_extension d hd Jc)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (D : @Paper.lane4_deterministic_good_scale_input d ⟨by omega⟩) (i : Fin d) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
        (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∃ hmem : ∀ K, MemLp (fun omega => Book.Ch02.sigmaCoarse
            (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i i) 1
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
          Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0))
            (aux_g9_sigma_entries_compact_A Jc M H omega K) i i)))) := by
  obtain ⟨delta1, hdelta1, hall⟩ := g9_dirichlet_response_compact d hd Jc Pc Xc W Sf D
    (Pi.single i 1) (fun h => by simpa using congrFun h i)
  refine ⟨delta1, hdelta1, ?_⟩
  intro M Rm Sreg It H hH hM
  obtain ⟨hmem, hcompact2⟩ := hall M Rm Sreg It H hH hM
  have heqfun : (fun (K : ℕ) (omega : BilateralField d) => Book.Ch02.sigmaCoarse
      (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i i) =
      (fun K omega => affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
        aux_lem_prefix_limit_atom_extraction_poincare.1
        (cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1)) := by
    funext K omega
    exact aux_g9_sigma_entries_compact_diag Jc M H omega K i
  have hpq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := hp2.out
  have hmem1 : ∀ K, MemLp (fun omega => Book.Ch02.sigmaCoarse
      (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i i) 1
      (chaosSampleLaw M).toMeasure := by
    intro K
    have := (hmem K).mono_exponent hpq
    rwa [show (fun omega => Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0))
        (aux_g9_sigma_entries_compact_A Jc M H omega K) i i) =
        (fun omega => affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
          aux_lem_prefix_limit_atom_extraction_poincare.1
          (cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1)) from
      congrFun heqfun K]
  refine ⟨hmem1, ?_⟩
  have hrep : (fun K => (hmem1 K).toLp (fun omega => Book.Ch02.sigmaCoarse
      (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i i)) =
      (fun K => ((hmem K).mono_exponent hpq).toLp (fun omega =>
        affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
          aux_lem_prefix_limit_atom_extraction_poincare.1
          (cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1))) := by
    funext K
    exact MemLp.toLp_congr (hmem1 K) ((hmem K).mono_exponent hpq)
      (Filter.EventuallyEq.of_eq (congrFun heqfun K))
  rw [hrep]
  exact isCompact_closure_range_mono_exponent hpq hmem hcompact2

/-- Off-diagonal case compactness: `sigmaCoarse (i,j)`, `i ≠ j`, is, as a family over `K`,
integrable and relatively compact in `L¹`, via the three-term polarization combined with
the reusable `isCompact_closure_range_combo3` combinator. -/
theorem aux_g9_sigma_entries_compact_offdiag_compact
    (Jc : Paper.in_J d) (Pc : Paper.in_poincare d hd Jc) (Xc : Paper.in_extension d hd Jc)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (D : @Paper.lane4_deterministic_good_scale_input d ⟨by omega⟩) (i j : Fin d) (hij : i ≠ j) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
        (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∃ hmem : ∀ K, MemLp (fun omega => Book.Ch02.sigmaCoarse
            (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i j) 1
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
          Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0))
            (aux_g9_sigma_entries_compact_A Jc M H omega K) i j)))) := by
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
  obtain ⟨hmemq1, hcq1⟩ := hall1 M Rm Sreg It H hH hM1
  obtain ⟨hmemq2, hcq2⟩ := hall2 M Rm Sreg It H hH hM2
  obtain ⟨hmemq3, hcq3⟩ := hall3 M Rm Sreg It H hH hM3
  have hpq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := hp2.out
  refine isCompact_closure_range_combo3 (2⁻¹ : ℝ) (-2⁻¹ : ℝ) (-2⁻¹ : ℝ)
    (fun K => (hmemq1 K).mono_exponent hpq) (fun K => (hmemq2 K).mono_exponent hpq)
    (fun K => (hmemq3 K).mono_exponent hpq) (isCompact_closure_range_mono_exponent hpq hmemq1 hcq1)
    (isCompact_closure_range_mono_exponent hpq hmemq2 hcq2)
    (isCompact_closure_range_mono_exponent hpq hmemq3 hcq3) (fun K => Filter.EventuallyEq.of_eq ?_)
  funext omega
  have hpt := aux_g9_sigma_entries_compact_offdiag Jc M H omega K i j hij
  linarith [hpt]

/-- Diagonal `sigmaStarInvCoarse (i,i)` compactness, CONDITIONAL on `NeumannResponseCompactAtOrigin`
(see its docstring for exactly what remains open). -/
theorem aux_g9_sigma_entries_compact_starinv_diag_compact
    (hNeumann : NeumannResponseCompactAtOrigin d)
    (Jc : Paper.in_J d) (i : Fin d) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
        (Sreg : Paper.in_6_16 d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∃ hmem : ∀ K, MemLp (fun omega => Book.Ch02.sigmaStarInvCoarse
            (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i i) 1
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
          Book.Ch02.sigmaStarInvCoarse (cubeDomain (Homogenization.originCube d 0))
            (aux_g9_sigma_entries_compact_A Jc M H omega K) i i)))) := by
  obtain ⟨delta1, hdelta1, hall⟩ := hNeumann (Pi.single i 1) (fun h => by simpa using congrFun h i)
  refine ⟨delta1, hdelta1, ?_⟩
  intro M Rm Sreg H hH hM
  obtain ⟨hmem, hcompact2⟩ := hall M Rm Sreg H hH hM
  have heqfun : (fun (K : ℕ) (omega : BilateralField d) => Book.Ch02.sigmaStarInvCoarse
      (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i i) =
      (fun K omega => affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
        (cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1)) := by
    funext K omega
    exact aux_g9_sigma_entries_compact_starinv_diag Jc M H omega K i
  have hpq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := hp2.out
  have hmem1 : ∀ K, MemLp (fun omega => Book.Ch02.sigmaStarInvCoarse
      (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i i) 1
      (chaosSampleLaw M).toMeasure := by
    intro K
    have := (hmem K).mono_exponent hpq
    rwa [congrFun heqfun K]
  refine ⟨hmem1, ?_⟩
  have hrep : (fun K => (hmem1 K).toLp (fun omega => Book.Ch02.sigmaStarInvCoarse
      (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i i)) =
      (fun K => ((hmem K).mono_exponent hpq).toLp (fun omega =>
        affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2
          (cutoffPositiveCoefficient M H omega K 0 one_pos) (Pi.single i 1))) := by
    funext K
    exact MemLp.toLp_congr (hmem1 K) ((hmem K).mono_exponent hpq)
      (Filter.EventuallyEq.of_eq (congrFun heqfun K))
  rw [hrep]
  exact isCompact_closure_range_mono_exponent hpq hmem hcompact2

/-- Off-diagonal `sigmaStarInvCoarse (i,j)`, `i ≠ j`, compactness, CONDITIONAL on
`NeumannResponseCompactAtOrigin`. -/
theorem aux_g9_sigma_entries_compact_starinv_offdiag_compact
    (hNeumann : NeumannResponseCompactAtOrigin d)
    (Jc : Paper.in_J d) (i j : Fin d) (hij : i ≠ j) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
        (Sreg : Paper.in_6_16 d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∃ hmem : ∀ K, MemLp (fun omega => Book.Ch02.sigmaStarInvCoarse
            (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i j) 1
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
          Book.Ch02.sigmaStarInvCoarse (cubeDomain (Homogenization.originCube d 0))
            (aux_g9_sigma_entries_compact_A Jc M H omega K) i j)))) := by
  obtain ⟨d1, h1, hall1⟩ := hNeumann (Pi.single i 1 + Pi.single j 1) (by
    intro h
    have := congrFun h i
    simp [hij.symm] at this)
  obtain ⟨d2, h2, hall2⟩ := hNeumann (Pi.single i 1) (fun h => by simpa using congrFun h i)
  obtain ⟨d3, h3, hall3⟩ := hNeumann (Pi.single j 1) (fun h => by simpa using congrFun h j)
  refine ⟨min d1 (min d2 d3), lt_min h1 (lt_min h2 h3), ?_⟩
  intro M Rm Sreg H hH hM
  have hM1 : M.delta ≤ min 1 d1 := hM.trans (min_le_min_left 1 (min_le_left _ _))
  have hM2 : M.delta ≤ min 1 d2 := hM.trans (min_le_min_left 1 ((min_le_right _ _).trans (min_le_left _ _)))
  have hM3 : M.delta ≤ min 1 d3 := hM.trans (min_le_min_left 1 ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hmemq1, hcq1⟩ := hall1 M Rm Sreg H hH hM1
  obtain ⟨hmemq2, hcq2⟩ := hall2 M Rm Sreg H hH hM2
  obtain ⟨hmemq3, hcq3⟩ := hall3 M Rm Sreg H hH hM3
  have hpq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := hp2.out
  refine isCompact_closure_range_combo3 (2⁻¹ : ℝ) (-2⁻¹ : ℝ) (-2⁻¹ : ℝ)
    (fun K => (hmemq1 K).mono_exponent hpq) (fun K => (hmemq2 K).mono_exponent hpq)
    (fun K => (hmemq3 K).mono_exponent hpq) (isCompact_closure_range_mono_exponent hpq hmemq1 hcq1)
    (isCompact_closure_range_mono_exponent hpq hmemq2 hcq2)
    (isCompact_closure_range_mono_exponent hpq hmemq3 hcq3) (fun K => Filter.EventuallyEq.of_eq ?_)
  funext omega
  have hpt := aux_g9_sigma_entries_compact_starinv_offdiag Jc M H omega K i j hij
  linarith [hpt]

/-- Paper `mfd:sec-local-form` (Section 9), the `sigmaCoarse` half of the cell matrix family
in `lem_prefix_limit_g9_cell_compact`: for the identity chart on the origin cube and any pair of
directions `(i,j)`, the coarse Dirichlet coefficient entry is, as a family over the cutoff `K`,
integrable and relatively compact in `L¹` -- fully unconditional (Dirichlet side only; see
`aux_g9_sigma_entries_compact_starinv_diag_compact`/`_starinv_offdiag_compact` for the
`sigmaStarInvCoarse`/Neumann mirror, which needs `NeumannResponseCompactAtOrigin`). -/
theorem g9_sigma_entries_compact
    (Jc : Paper.in_J d) (Pc : Paper.in_poincare d hd Jc) (Xc : Paper.in_extension d hd Jc)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (D : @Paper.lane4_deterministic_good_scale_input d ⟨by omega⟩) (i j : Fin d) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
        (Sreg : Paper.in_6_16 d M) (It : Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∃ hmem : ∀ K, MemLp (fun omega => Book.Ch02.sigmaCoarse
            (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i j) 1
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
          Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0))
            (aux_g9_sigma_entries_compact_A Jc M H omega K) i j)))) := by
  by_cases hij : i = j
  · subst hij
    exact aux_g9_sigma_entries_compact_diag_compact hd Jc Pc Xc W Sf D i
  · exact aux_g9_sigma_entries_compact_offdiag_compact hd Jc Pc Xc W Sf D i j hij

end Paper
