module

public import SubdiffusiveProcess.Paper.g9_sigma_entries_compact
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Analysis.LipschitzLpCompact

@[expose] public section

open MeasureTheory SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity Homogenization Set
open TopologicalSpace Homogenization.Book.Ch02
open scoped ENNReal NNReal
open scoped Matrix.Norms.Elementwise
open WithLp
open scoped Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)]

/-- The scalar function combining the `d²` matrix entries into `Homogenization.Book.Ch02.matrixNorm`,
as a function of the flattened `Fin d × Fin d`-indexed entry tuple. -/
def aux_g9_matrixnorm_entries_compact_g (d : ℕ) : (Fin d × Fin d → ℝ) → ℝ :=
  fun entries => matrixNorm (fun i j => entries (i, j))

omit [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] hp2 in
theorem aux_g9_matrixnorm_entries_compact_g0
    [_portSection0 : NeZero d] [_portSection1 : MeasurableSpace C(SpatialCoordinates d, ℝ)] [_portSection2 : BorelSpace C(SpatialCoordinates d, ℝ)] [_portSection3 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)] : aux_g9_matrixnorm_entries_compact_g d 0 = 0 := by
  unfold aux_g9_matrixnorm_entries_compact_g
  show matrixNorm (0 : Matrix (Fin d) (Fin d) ℝ) = 0
  unfold matrixNorm
  simp

omit [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] hp2 in
theorem aux_g9_matrixnorm_entries_compact_glip
    [_portSection0 : NeZero d] [_portSection1 : MeasurableSpace C(SpatialCoordinates d, ℝ)] [_portSection2 : BorelSpace C(SpatialCoordinates d, ℝ)] [_portSection3 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)] :
    ∀ u v : Fin d × Fin d → ℝ,
      |aux_g9_matrixnorm_entries_compact_g d u - aux_g9_matrixnorm_entries_compact_g d v| ≤
        (Fintype.card (Fin d) : ℝ) * ∑ p, |u p - v p| := by
  intro u v
  unfold aux_g9_matrixnorm_entries_compact_g
  refine (matrixNorm_lipschitz (fun i j => u (i, j)) (fun i j => v (i, j))).trans ?_
  apply le_of_eq
  congr 1
  rw [← Fintype.sum_prod_type']

/-- The identity chart on the origin cube, at cutoff `K`: the same `TriadicCoeffFamily` argument
`lem_prefix_limit_g9_cell_compact`'s own `F K omega` uses, and definitionally the value whose
`coeffOn` restriction is `aux_g9_sigma_entries_compact_A`. -/
def aux_g9_matrixnorm_entries_compact_F (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (K : ℕ) : Homogenization.Book.Ch02.TriadicCoeffFamily d :=
  I.chart 0 1 one_pos (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1

omit [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] hp2 in
theorem aux_g9_matrixnorm_entries_compact_F_coeffOn
    [_portSection0 : NeZero d] [_portSection1 : MeasurableSpace C(SpatialCoordinates d, ℝ)] [_portSection2 : BorelSpace C(SpatialCoordinates d, ℝ)] [_portSection3 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)] (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (K : ℕ) :
    (aux_g9_matrixnorm_entries_compact_F I M H omega K).coeffOn (Homogenization.originCube d 0) =
      aux_g9_sigma_entries_compact_A I M H omega K := rfl

theorem aux_g9_matrixnorm_entries_compact_bCoarse_eq_sigmaCoarse (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (K : ℕ) :
    Book.Ch02.coarseBMatrixNorm (Homogenization.originCube d 0)
        (aux_g9_matrixnorm_entries_compact_F I M H omega K) =
      aux_g9_matrixnorm_entries_compact_g d
        (fun p => Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0))
          (aux_g9_sigma_entries_compact_A I M H omega K) p.1 p.2) := by
  unfold Book.Ch02.coarseBMatrixNorm aux_g9_matrixnorm_entries_compact_g
  rw [aux_g9_matrixnorm_entries_compact_F_coeffOn]
  have hsym := aux_g9_sigma_entries_compact_symm I M H omega K
  have hderived := (responseSymmetricDirichletNeumannTheory (cubeDomain (Homogenization.originCube d 0))
    (aux_g9_sigma_entries_compact_A I M H omega K) hsym).derived_matrices
  rw [hderived.2.2]

/-- Paper `mfd:sec-local-form` (Section 9), the `coarseBMatrixNorm` half of the cell matrix
family in `lem_prefix_limit_g9_cell_compact`, at the unit root cell only: for the identity chart
on the origin cube, the `|b|` matrix norm observable is, as a family over the cutoff `K`,
integrable and relatively compact in `L¹`, fully unconditional (Dirichlet side only). Combines
`g9_sigma_entries_compact`'s entrywise `sigmaCoarse` compactness (all `d²` entries at once) with
`derived_matrices` (`bCoarse = sigmaCoarse` for a symmetric coefficient) and the reusable
Lipschitz-combination tool `isCompact_closure_range_lipschitz_combo`. -/
theorem aux_g9_matrixnorm_entries_compact_step
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hall' : ∀ p : Fin d × Fin d,
      ∃ hmem : ∀ K, MemLp (fun omega => Book.Ch02.sigmaCoarse
          (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K)
          p.1 p.2) 1 (chaosSampleLaw M).toMeasure,
      IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
        Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0))
          (aux_g9_sigma_entries_compact_A Jc M H omega K) p.1 p.2))))) :
    ∃ hmem : ∀ K, MemLp (fun omega => Book.Ch02.coarseBMatrixNorm
        (Homogenization.originCube d 0) (aux_g9_matrixnorm_entries_compact_F Jc M H omega K)) 1
      (chaosSampleLaw M).toMeasure,
    IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
      Book.Ch02.coarseBMatrixNorm (Homogenization.originCube d 0)
        (aux_g9_matrixnorm_entries_compact_F Jc M H omega K))))) := by
  choose hmemEntry hcompactEntry using hall'
  set f2 : Fin d × Fin d → ℕ → BilateralField d → ℝ := fun p K omega =>
    Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0))
      (aux_g9_sigma_entries_compact_A Jc M H omega K) p.1 p.2 with hf2def
  obtain ⟨hcombMem, hcombCompact⟩ := isCompact_closure_range_lipschitz_combo
    (f := f2) (hmem := hmemEntry) (hf := hcompactEntry)
    (g := aux_g9_matrixnorm_entries_compact_g d) (c := (Fintype.card (Fin d) : ℝ))
    (hc := by positivity) (hg0 := aux_g9_matrixnorm_entries_compact_g0)
    (hglip := aux_g9_matrixnorm_entries_compact_glip)
  have heqfun : (fun (K : ℕ) (omega : BilateralField d) => Book.Ch02.coarseBMatrixNorm
      (Homogenization.originCube d 0) (aux_g9_matrixnorm_entries_compact_F Jc M H omega K)) =
      (fun K omega => aux_g9_matrixnorm_entries_compact_g d
        (fun p => Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0))
          (aux_g9_sigma_entries_compact_A Jc M H omega K) p.1 p.2)) := by
    funext K omega
    exact aux_g9_matrixnorm_entries_compact_bCoarse_eq_sigmaCoarse Jc M H omega K
  have hmem1 : ∀ K, MemLp (fun omega => Book.Ch02.coarseBMatrixNorm
      (Homogenization.originCube d 0) (aux_g9_matrixnorm_entries_compact_F Jc M H omega K)) 1
      (chaosSampleLaw M).toMeasure := by
    intro K
    rw [show (fun omega => Book.Ch02.coarseBMatrixNorm (Homogenization.originCube d 0)
        (aux_g9_matrixnorm_entries_compact_F Jc M H omega K)) =
        (fun omega => aux_g9_matrixnorm_entries_compact_g d
          (fun p => Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0))
            (aux_g9_sigma_entries_compact_A Jc M H omega K) p.1 p.2)) from
      congrFun heqfun K]
    exact hcombMem K
  refine ⟨hmem1, ?_⟩
  have hrep : (fun K => (hmem1 K).toLp (fun omega => Book.Ch02.coarseBMatrixNorm
      (Homogenization.originCube d 0) (aux_g9_matrixnorm_entries_compact_F Jc M H omega K))) =
      (fun K => (hcombMem K).toLp (fun omega => aux_g9_matrixnorm_entries_compact_g d
        (fun p => Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0))
          (aux_g9_sigma_entries_compact_A Jc M H omega K) p.1 p.2))) := by
    funext K
    exact MemLp.toLp_congr (hmem1 K) (hcombMem K) (Filter.EventuallyEq.of_eq (congrFun heqfun K))
  rw [hrep]
  exact hcombCompact

/-- Paper `mfd:sec-local-form` (Section 9), the `coarseBMatrixNorm` half of the cell matrix
family in `lem_prefix_limit_g9_cell_compact`, at the unit root cell only: for the identity chart
on the origin cube, the `|b|` matrix norm observable is, as a family over the cutoff `K`,
integrable and relatively compact in `L¹`, fully unconditional (Dirichlet side only). Combines
`g9_sigma_entries_compact`'s entrywise `sigmaCoarse` compactness (all `d²` entries at once) with
`derived_matrices` (`bCoarse = sigmaCoarse` for a symmetric coefficient) and the reusable
Lipschitz-combination tool `isCompact_closure_range_lipschitz_combo`. -/
theorem g9_matrixnorm_entries_compact
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (D : @_root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d ⟨by omega⟩) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ min 1 delta0 →
        ∃ hmem : ∀ K, MemLp (fun omega => Book.Ch02.coarseBMatrixNorm
            (Homogenization.originCube d 0) (aux_g9_matrixnorm_entries_compact_F Jc M H omega K)) 1
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
          Book.Ch02.coarseBMatrixNorm (Homogenization.originCube d 0)
            (aux_g9_matrixnorm_entries_compact_F Jc M H omega K))))) := by
  have hentry : ∀ p : Fin d × Fin d,
      ∃ delta1 : ℝ, 0 < delta1 ∧
        ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
          (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H),
          M.delta ≤ min 1 delta1 →
          ∃ hmem : ∀ K, MemLp (fun omega => Book.Ch02.sigmaCoarse
              (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K)
              p.1 p.2) 1 (chaosSampleLaw M).toMeasure,
          IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
            Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0))
              (aux_g9_sigma_entries_compact_A Jc M H omega K) p.1 p.2)))) :=
    fun p => g9_sigma_entries_compact hd Jc Pc Xc W Sf D p.1 p.2
  choose delta1 hdelta1pos hall using hentry
  have hne : (Finset.univ : Finset (Fin d × Fin d)).Nonempty := Finset.univ_nonempty
  refine ⟨Finset.univ.inf' hne delta1, (Finset.lt_inf'_iff hne).mpr (fun p _ => hdelta1pos p), ?_⟩
  intro M Rm Sreg It H hH hM
  have hMp : ∀ p : Fin d × Fin d, M.delta ≤ min 1 (delta1 p) := by
    intro p
    refine hM.trans (min_le_min_left 1 ?_)
    exact Finset.inf'_le delta1 (Finset.mem_univ p)
  exact aux_g9_matrixnorm_entries_compact_step Jc M H
    (fun p => hall p M Rm Sreg It H hH (hMp p))

theorem aux_g9_matrixnorm_entries_compact_starinv_eq (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (K : ℕ) :
    Book.Ch02.coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
        (aux_g9_matrixnorm_entries_compact_F I M H omega K) =
      aux_g9_matrixnorm_entries_compact_g d
        (fun p => Book.Ch02.sigmaStarInvCoarse (cubeDomain (Homogenization.originCube d 0))
          (aux_g9_sigma_entries_compact_A I M H omega K) p.1 p.2) := by
  unfold Book.Ch02.coarseSigmaStarInvMatrixNorm aux_g9_matrixnorm_entries_compact_g
  rw [aux_g9_matrixnorm_entries_compact_F_coeffOn]

/-- The `sigmaStarInvCoarse (i,j)` entry compactness, any `(i,j)`, CONDITIONAL on
`NeumannResponseCompactAtOrigin` -- combining `g9_sigma_entries_compact.lean`'s split
diagonal/off-diagonal Neumann results the same way its own `g9_sigma_entries_compact` combines
the Dirichlet ones. -/
theorem aux_g9_matrixnorm_entries_compact_starinv_entry
    (hNeumann : NeumannResponseCompactAtOrigin d) (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (i j : Fin d) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (_Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_hH : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∃ hmem : ∀ K, MemLp (fun omega => Book.Ch02.sigmaStarInvCoarse
            (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K) i j) 1
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
          Book.Ch02.sigmaStarInvCoarse (cubeDomain (Homogenization.originCube d 0))
            (aux_g9_sigma_entries_compact_A Jc M H omega K) i j)))) := by
  by_cases hij : i = j
  · subst hij
    exact aux_g9_sigma_entries_compact_starinv_diag_compact hNeumann Jc i
  · exact aux_g9_sigma_entries_compact_starinv_offdiag_compact hNeumann Jc i j hij

theorem aux_g9_matrixnorm_entries_compact_starinv_step
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hall' : ∀ p : Fin d × Fin d,
      ∃ hmem : ∀ K, MemLp (fun omega => Book.Ch02.sigmaStarInvCoarse
          (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K)
          p.1 p.2) 1 (chaosSampleLaw M).toMeasure,
      IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
        Book.Ch02.sigmaStarInvCoarse (cubeDomain (Homogenization.originCube d 0))
          (aux_g9_sigma_entries_compact_A Jc M H omega K) p.1 p.2))))) :
    ∃ hmem : ∀ K, MemLp (fun omega => Book.Ch02.coarseSigmaStarInvMatrixNorm
        (Homogenization.originCube d 0) (aux_g9_matrixnorm_entries_compact_F Jc M H omega K)) 1
      (chaosSampleLaw M).toMeasure,
    IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
      Book.Ch02.coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
        (aux_g9_matrixnorm_entries_compact_F Jc M H omega K))))) := by
  choose hmemEntry hcompactEntry using hall'
  set f2 : Fin d × Fin d → ℕ → BilateralField d → ℝ := fun p K omega =>
    Book.Ch02.sigmaStarInvCoarse (cubeDomain (Homogenization.originCube d 0))
      (aux_g9_sigma_entries_compact_A Jc M H omega K) p.1 p.2 with hf2def
  obtain ⟨hcombMem, hcombCompact⟩ := isCompact_closure_range_lipschitz_combo
    (f := f2) (hmem := hmemEntry) (hf := hcompactEntry)
    (g := aux_g9_matrixnorm_entries_compact_g d) (c := (Fintype.card (Fin d) : ℝ))
    (hc := by positivity) (hg0 := aux_g9_matrixnorm_entries_compact_g0)
    (hglip := aux_g9_matrixnorm_entries_compact_glip)
  have heqfun : (fun (K : ℕ) (omega : BilateralField d) => Book.Ch02.coarseSigmaStarInvMatrixNorm
      (Homogenization.originCube d 0) (aux_g9_matrixnorm_entries_compact_F Jc M H omega K)) =
      (fun K omega => aux_g9_matrixnorm_entries_compact_g d
        (fun p => Book.Ch02.sigmaStarInvCoarse (cubeDomain (Homogenization.originCube d 0))
          (aux_g9_sigma_entries_compact_A Jc M H omega K) p.1 p.2)) := by
    funext K omega
    exact aux_g9_matrixnorm_entries_compact_starinv_eq Jc M H omega K
  have hmem1 : ∀ K, MemLp (fun omega => Book.Ch02.coarseSigmaStarInvMatrixNorm
      (Homogenization.originCube d 0) (aux_g9_matrixnorm_entries_compact_F Jc M H omega K)) 1
      (chaosSampleLaw M).toMeasure := by
    intro K
    rw [show (fun omega => Book.Ch02.coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
        (aux_g9_matrixnorm_entries_compact_F Jc M H omega K)) =
        (fun omega => aux_g9_matrixnorm_entries_compact_g d
          (fun p => Book.Ch02.sigmaStarInvCoarse (cubeDomain (Homogenization.originCube d 0))
            (aux_g9_sigma_entries_compact_A Jc M H omega K) p.1 p.2)) from
      congrFun heqfun K]
    exact hcombMem K
  refine ⟨hmem1, ?_⟩
  have hrep : (fun K => (hmem1 K).toLp (fun omega => Book.Ch02.coarseSigmaStarInvMatrixNorm
      (Homogenization.originCube d 0) (aux_g9_matrixnorm_entries_compact_F Jc M H omega K))) =
      (fun K => (hcombMem K).toLp (fun omega => aux_g9_matrixnorm_entries_compact_g d
        (fun p => Book.Ch02.sigmaStarInvCoarse (cubeDomain (Homogenization.originCube d 0))
          (aux_g9_sigma_entries_compact_A Jc M H omega K) p.1 p.2))) := by
    funext K
    exact MemLp.toLp_congr (hmem1 K) (hcombMem K) (Filter.EventuallyEq.of_eq (congrFun heqfun K))
  rw [hrep]
  exact hcombCompact

/-- Paper `mfd:sec-local-form` (Section 9), the `coarseSigmaStarInvMatrixNorm` half of the cell
matrix family in `lem_prefix_limit_g9_cell_compact`, at the unit root cell only: for the identity
chart on the origin cube, the `|σ_*^{-1}|` matrix norm observable is, as a family over the cutoff
`K`, integrable and relatively compact in `L¹`, CONDITIONAL on `NeumannResponseCompactAtOrigin`
(the Neumann mirror of `g9_dirichlet_response_compact`, retained here as an explicit hypothesis; see
`g9_sigma_entries_compact.lean`'s own docstring). Combines the entrywise `sigmaStarInvCoarse`
compactness (all `d²` entries, via `aux_g9_sigma_entries_compact_starinv_diag_compact`/
`_offdiag_compact`) with the reusable Lipschitz-combination tool
`isCompact_closure_range_lipschitz_combo` (no `derived_matrices` step needed here:
`coarseSigmaStarInvMatrixNorm` is `matrixNorm ∘ sigmaStarInvCoarse` directly). -/
theorem aux_g9_matrixnorm_entries_compact_starinv
    (hNeumann : NeumannResponseCompactAtOrigin d) (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (_Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ min 1 delta0 →
        ∃ hmem : ∀ K, MemLp (fun omega => Book.Ch02.coarseSigmaStarInvMatrixNorm
            (Homogenization.originCube d 0) (aux_g9_matrixnorm_entries_compact_F Jc M H omega K)) 1
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
          Book.Ch02.coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
            (aux_g9_matrixnorm_entries_compact_F Jc M H omega K))))) := by
  have hentry : ∀ p : Fin d × Fin d,
      ∃ delta1 : ℝ, 0 < delta1 ∧
        ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
          (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
          (hH : InfraredCharacterization M H),
          M.delta ≤ min 1 delta1 →
          ∃ hmem : ∀ K, MemLp (fun omega => Book.Ch02.sigmaStarInvCoarse
              (cubeDomain (Homogenization.originCube d 0)) (aux_g9_sigma_entries_compact_A Jc M H omega K)
              p.1 p.2) 1 (chaosSampleLaw M).toMeasure,
          IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
            Book.Ch02.sigmaStarInvCoarse (cubeDomain (Homogenization.originCube d 0))
              (aux_g9_sigma_entries_compact_A Jc M H omega K) p.1 p.2)))) :=
    fun p => aux_g9_matrixnorm_entries_compact_starinv_entry hNeumann Jc p.1 p.2
  choose delta1 hdelta1pos hall using hentry
  have hne : (Finset.univ : Finset (Fin d × Fin d)).Nonempty := Finset.univ_nonempty
  refine ⟨Finset.univ.inf' hne delta1, (Finset.lt_inf'_iff hne).mpr (fun p _ => hdelta1pos p), ?_⟩
  intro M Rm Sreg H hH hM
  have hMp : ∀ p : Fin d × Fin d, M.delta ≤ min 1 (delta1 p) := by
    intro p
    refine hM.trans (min_le_min_left 1 ?_)
    exact Finset.inf'_le delta1 (Finset.mem_univ p)
  exact aux_g9_matrixnorm_entries_compact_starinv_step Jc M H
    (fun p => hall p M Rm Sreg H hH (hMp p))

end SubdiffusiveProcess.Paper
