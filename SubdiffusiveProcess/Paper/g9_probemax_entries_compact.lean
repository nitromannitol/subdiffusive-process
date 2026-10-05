module

public import SubdiffusiveProcess.Paper.g9_sigma_entries_compact
public import SubdiffusiveProcess.CoarseGrainingVocab.PrefixSuffixMeasurability
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic
public import SubdiffusiveProcess.Analysis.LipschitzLpCompact

@[expose] public section

open MeasureTheory SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity Homogenization Set
open TopologicalSpace Homogenization.Book.Ch02
open scoped ENNReal NNReal Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)]

/-- The identity chart on the origin cube, at cutoff `K` -- the same `F K omega`
`lem_prefix_limit_g9_cell_compact` uses. -/
def aux_g9_probemax_entries_compact_F (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (K : ℕ) : Homogenization.Book.Ch02.TriadicCoeffFamily d :=
  I.chart 0 1 one_pos (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1

omit [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] hp2 in
theorem aux_g9_probemax_entries_compact_F_coeffOn
    [_portSection0 : NeZero d] [_portSection1 : MeasurableSpace C(SpatialCoordinates d, ℝ)] [_portSection2 : BorelSpace C(SpatialCoordinates d, ℝ)] [_portSection3 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)] (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (K : ℕ) :
    (aux_g9_probemax_entries_compact_F I M H omega K).coeffOn (Homogenization.originCube d 0) =
      aux_g9_sigma_entries_compact_A I M H omega K := rfl

/-- The deterministic reference matrix whose operator norm is `paperScalarProbeMax` at
`alpha = 1`: half the sum of the Dirichlet and Neumann coarse matrices, minus the identity. -/
def aux_g9_probemax_entries_compact_R {d : ℕ} (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) :
    Mat d :=
  (1 / 2 : ℝ) • Book.Ch02.sigmaCoarse U a + (1 / 2 : ℝ) • Book.Ch02.sigmaStarInvCoarse U a -
    (1 : Mat d)

omit hp2 in
theorem aux_g9_probemax_entries_compact_vecDot_sub_right
    [_portSection0 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)] {d : ℕ} (x y z : Vec d) :
    vecDot x (y - z) = vecDot x y - vecDot x z := by
  simp only [vecDot, Pi.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]

theorem aux_g9_probemax_entries_compact_R_quad {d : ℕ} (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) (hsym : Book.Ch02.CoeffOn.IsSymmetric a) (x : Vec d) :
    vecDot x (matVecMul (aux_g9_probemax_entries_compact_R U a) x) = responseJ U a x x := by
  have hthy := responseSymmetricDirichletNeumannTheory U a hsym
  have hsplit := hthy.response_dirichlet_neumann_split x x
  have hd1 := hthy.dirichlet_value_by_sigma x
  have hn1 := hthy.neumann_value_by_sigmaStarInv x
  have hone : matVecMul (1 : Mat d) x = x := by
    show (1 : Mat d) *ᵥ x = x
    exact Matrix.one_mulVec x
  have hexpand : matVecMul (aux_g9_probemax_entries_compact_R U a) x =
      (1 / 2 : ℝ) • matVecMul (Book.Ch02.sigmaCoarse U a) x +
        (1 / 2 : ℝ) • matVecMul (Book.Ch02.sigmaStarInvCoarse U a) x - x := by
    unfold aux_g9_probemax_entries_compact_R
    rw [sub_matVecMul, add_matVecMul, smul_matVecMul, smul_matVecMul, hone]
  rw [hexpand, aux_g9_probemax_entries_compact_vecDot_sub_right, vecDot_add_right,
    vecDot_smul_right, vecDot_smul_right, hsplit, hd1, hn1]

theorem aux_g9_probemax_entries_compact_R_posSemidef {d : ℕ} (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) (hsym : Book.Ch02.CoeffOn.IsSymmetric a) :
    (aux_g9_probemax_entries_compact_R U a).PosSemidef := by
  have hSymmR : (aux_g9_probemax_entries_compact_R U a).IsSymm := by
    have h1 : (Book.Ch02.sigmaCoarse U a).IsSymm := sigmaCoarse_isSymm U a
    have h2 : (Book.Ch02.sigmaStarInvCoarse U a).IsSymm := sigmaStarInvCoarse_isSymm U a
    have h3 : (1 : Mat d).IsSymm := Matrix.isSymm_one
    unfold aux_g9_probemax_entries_compact_R
    exact ((h1.smul (1 / 2 : ℝ)).add (h2.smul (1 / 2 : ℝ))).sub h3
  have hzero : (0 : Mat d).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · simp [Matrix.IsHermitian]
    · intro x; simp
  have hLoewner : MatLoewnerLE 0 (aux_g9_probemax_entries_compact_R U a) := by
    intro x
    have hq := aux_g9_probemax_entries_compact_R_quad U a hsym x
    have hnn : 0 ≤ responseJ U a x x := responseJ_nonneg U a x x
    have hzero_mv : matVecMul (0 : Mat d) x = 0 := by
      show (0 : Mat d) *ᵥ x = 0
      simp
    rw [hzero_mv, vecDot_zero_right, hq]
    linarith
  exact posSemidef_of_matLoewnerLE_of_posSemidef_of_isSymm hzero hSymmR hLoewner

theorem aux_g9_probemax_entries_compact_R_hquad {d : ℕ} (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) (hsym : Book.Ch02.CoeffOn.IsSymmetric a) (e : Vec d) :
    SubdiffusiveProcess.CoarseGrainingVocab.J U a ((Real.sqrt 1)⁻¹ • e) (Real.sqrt 1 • e) =
      vecDot e (matVecMul (aux_g9_probemax_entries_compact_R U a) e) := by
  rw [Real.sqrt_one, inv_one, one_smul]
  exact (aux_g9_probemax_entries_compact_R_quad U a hsym e).symm

/-- `paperScalarProbeMax` at `alpha = 1`, reduced to the operator norm of
`aux_g9_probemax_entries_compact_R`. -/
theorem aux_g9_probemax_entries_compact_reduction {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    (hsym : Book.Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax Q a 1 =
      ENNReal.ofReal
        (matrixOperatorNorm (aux_g9_probemax_entries_compact_R (cubeDomain Q) (a.coeffOn Q))) := by
  show SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMaxOn (cubeDomain Q) (a.coeffOn Q) 1 = _
  exact SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMaxOn_eq_ofReal_matrixOperatorNorm
    (cubeDomain Q) (a.coeffOn Q) 1 (aux_g9_probemax_entries_compact_R (cubeDomain Q) (a.coeffOn Q))
    (aux_g9_probemax_entries_compact_R_posSemidef (cubeDomain Q) (a.coeffOn Q) hsym)
    (aux_g9_probemax_entries_compact_R_hquad (cubeDomain Q) (a.coeffOn Q) hsym)

theorem aux_g9_probemax_entries_compact_toReal {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    (hsym : Book.Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) :
    (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax Q a 1).toReal =
      matrixOperatorNorm (aux_g9_probemax_entries_compact_R (cubeDomain Q) (a.coeffOn Q)) := by
  rw [aux_g9_probemax_entries_compact_reduction Q a hsym]
  exact ENNReal.toReal_ofReal (matrixOperatorNorm_nonneg _)

/-- The scalar function combining the sigma/sigmaStarInv/identity entries (flattened over
`Fin d × Fin d × Fin 3`, third coordinate `0`/`1`/`2` selecting sigma/sigmaStarInv/identity) into
`aux_g9_probemax_entries_compact_R`'s `matrixNorm`. -/
def aux_g9_probemax_entries_compact_g (d : ℕ) : (Fin d × Fin d × Fin 3 → ℝ) → ℝ :=
  fun entries => matrixNorm (fun i j =>
    (1 / 2 : ℝ) * (entries (i, j, 0) + entries (i, j, 1)) - entries (i, j, 2))

omit hp2 in
theorem aux_g9_probemax_entries_compact_g0
    [_portSection0 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)] (d : ℕ) [NeZero d] :
    aux_g9_probemax_entries_compact_g d 0 = 0 := by
  have hz : (fun i j : Fin d => (1 / 2 : ℝ) *
      ((0 : Fin d × Fin d × Fin 3 → ℝ) (i, j, 0) + (0 : Fin d × Fin d × Fin 3 → ℝ) (i, j, 1)) -
        (0 : Fin d × Fin d × Fin 3 → ℝ) (i, j, 2)) = (0 : Matrix (Fin d) (Fin d) ℝ) := by
    funext i j
    simp
  unfold aux_g9_probemax_entries_compact_g
  rw [hz]
  unfold matrixNorm
  simp

omit hp2 in
theorem aux_g9_probemax_entries_compact_glip
    [_portSection0 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)] (d : ℕ) :
    ∀ u v : Fin d × Fin d × Fin 3 → ℝ,
      |aux_g9_probemax_entries_compact_g d u - aux_g9_probemax_entries_compact_g d v| ≤
        (Fintype.card (Fin d) : ℝ) * ∑ p, |u p - v p| := by
  intro u v
  unfold aux_g9_probemax_entries_compact_g
  have hstep := matrixNorm_lipschitz
    (fun i j => (1 / 2 : ℝ) * (u (i, j, 0) + u (i, j, 1)) - u (i, j, 2))
    (fun i j => (1 / 2 : ℝ) * (v (i, j, 0) + v (i, j, 1)) - v (i, j, 2))
  refine hstep.trans ?_
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hbound : ∀ i j : Fin d,
      |((1 / 2 : ℝ) * (u (i, j, 0) + u (i, j, 1)) - u (i, j, 2)) -
        ((1 / 2 : ℝ) * (v (i, j, 0) + v (i, j, 1)) - v (i, j, 2))| ≤
      |u (i, j, 0) - v (i, j, 0)| + |u (i, j, 1) - v (i, j, 1)| + |u (i, j, 2) - v (i, j, 2)| := by
    intro i j
    have heq : ((1 / 2 : ℝ) * (u (i, j, 0) + u (i, j, 1)) - u (i, j, 2)) -
        ((1 / 2 : ℝ) * (v (i, j, 0) + v (i, j, 1)) - v (i, j, 2)) =
        (1 / 2 : ℝ) * (u (i, j, 0) - v (i, j, 0)) +
          ((1 / 2 : ℝ) * (u (i, j, 1) - v (i, j, 1)) + -(u (i, j, 2) - v (i, j, 2))) := by
      ring
    rw [heq]
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [neg_abs_le (u (i, j, 0) - v (i, j, 0)), neg_abs_le (u (i, j, 1) - v (i, j, 1)),
        le_abs_self (u (i, j, 2) - v (i, j, 2)), abs_nonneg (u (i, j, 0) - v (i, j, 0)),
        abs_nonneg (u (i, j, 1) - v (i, j, 1))]
    · linarith [le_abs_self (u (i, j, 0) - v (i, j, 0)), le_abs_self (u (i, j, 1) - v (i, j, 1)),
        neg_abs_le (u (i, j, 2) - v (i, j, 2)), abs_nonneg (u (i, j, 0) - v (i, j, 0)),
        abs_nonneg (u (i, j, 1) - v (i, j, 1))]
  refine (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hbound i j))).trans ?_
  have hsplit : ∀ i j : Fin d,
      |u (i, j, 0) - v (i, j, 0)| + |u (i, j, 1) - v (i, j, 1)| + |u (i, j, 2) - v (i, j, 2)| =
        ∑ k : Fin 3, |u (i, j, k) - v (i, j, k)| := by
    intro i j
    rw [Fin.sum_univ_three]
  simp_rw [hsplit]
  have hflat : (∑ p : Fin d × Fin d × Fin 3, |u p - v p|) =
      ∑ i, ∑ j, ∑ k, |u (i, j, k) - v (i, j, k)| := by
    rw [Fintype.sum_prod_type]
    congr 1
    funext i
    rw [Fintype.sum_prod_type]
  rw [hflat]

/-- The joint (sigma, sigmaStarInv, identity) family at index `(i,j,k)`, `k = 0/1/2`. -/
def aux_g9_probemax_entries_compact_triple (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (p : Fin d × Fin d × Fin 3) (K : ℕ) (omega : BilateralField d) : ℝ :=
  if p.2.2 = 0 then
    Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0))
      (aux_g9_sigma_entries_compact_A Jc M H omega K) p.1 p.2.1
  else if p.2.2 = 1 then
    Book.Ch02.sigmaStarInvCoarse (cubeDomain (Homogenization.originCube d 0))
      (aux_g9_sigma_entries_compact_A Jc M H omega K) p.1 p.2.1
  else if p.1 = p.2.1 then (1 : ℝ) else (0 : ℝ)

theorem aux_g9_probemax_entries_compact_triple_eq (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (K : ℕ) :
    (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax (Homogenization.originCube d 0)
        (aux_g9_probemax_entries_compact_F Jc M H omega K) 1).toReal =
      aux_g9_probemax_entries_compact_g d
        (fun p => aux_g9_probemax_entries_compact_triple Jc M H p K omega) := by
  have hsym : Book.Ch02.CoeffOn.IsSymmetric
      ((aux_g9_probemax_entries_compact_F Jc M H omega K).coeffOn (Homogenization.originCube d 0)) := by
    rw [aux_g9_probemax_entries_compact_F_coeffOn]
    exact aux_g9_sigma_entries_compact_symm Jc M H omega K
  rw [aux_g9_probemax_entries_compact_toReal (Homogenization.originCube d 0)
    (aux_g9_probemax_entries_compact_F Jc M H omega K) hsym,
    aux_g9_probemax_entries_compact_F_coeffOn]
  unfold aux_g9_probemax_entries_compact_R aux_g9_probemax_entries_compact_g
  congr 1
  funext i j
  have h10 : ¬ (1 : Fin 3) = 0 := by decide
  have h20 : ¬ (2 : Fin 3) = 0 := by decide
  have h21 : ¬ (2 : Fin 3) = 1 := by decide
  simp only [aux_g9_probemax_entries_compact_triple, ite_true, ite_eq_right h10, ite_eq_right h20,
    ite_eq_right h21, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, ite_true]
    ring
  · simp only [Matrix.one_apply_ne hij, ite_eq_right hij]
    ring

omit [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] hp2 in
theorem aux_g9_probemax_entries_compact_triple_zero
    [_portSection0 : NeZero d] [_portSection1 : MeasurableSpace C(SpatialCoordinates d, ℝ)] [_portSection2 : BorelSpace C(SpatialCoordinates d, ℝ)] [_portSection3 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)] (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (i j : Fin d) (K : ℕ) (omega : BilateralField d) :
    aux_g9_probemax_entries_compact_triple Jc M H (i, j, 0) K omega =
      Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0))
        (aux_g9_sigma_entries_compact_A Jc M H omega K) i j := rfl

omit [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] hp2 in
theorem aux_g9_probemax_entries_compact_triple_one
    [_portSection0 : NeZero d] [_portSection1 : MeasurableSpace C(SpatialCoordinates d, ℝ)] [_portSection2 : BorelSpace C(SpatialCoordinates d, ℝ)] [_portSection3 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)] (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (i j : Fin d) (K : ℕ) (omega : BilateralField d) :
    aux_g9_probemax_entries_compact_triple Jc M H (i, j, 1) K omega =
      Book.Ch02.sigmaStarInvCoarse (cubeDomain (Homogenization.originCube d 0))
        (aux_g9_sigma_entries_compact_A Jc M H omega K) i j := rfl

omit [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] hp2 in
theorem aux_g9_probemax_entries_compact_triple_two
    [_portSection0 : NeZero d] [_portSection1 : MeasurableSpace C(SpatialCoordinates d, ℝ)] [_portSection2 : BorelSpace C(SpatialCoordinates d, ℝ)] [_portSection3 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)] (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (i j : Fin d) (K : ℕ) (omega : BilateralField d) :
    aux_g9_probemax_entries_compact_triple Jc M H (i, j, 2) K omega =
      if i = j then (1 : ℝ) else (0 : ℝ) := by
  have h20 : ¬ (2 : Fin 3) = 0 := by decide
  have h21 : ¬ (2 : Fin 3) = 1 := by decide
  simp only [aux_g9_probemax_entries_compact_triple, ite_eq_right h20, ite_eq_right h21]

omit [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] hp2 in
/-- Constant family: the identity-matrix indicator does not depend on `K` or `omega`. -/
theorem aux_g9_probemax_entries_compact_const_compact
    [_portNZ : NeZero d] [_portMeas : MeasurableSpace C(SpatialCoordinates d, ℝ)] [_portBorel : BorelSpace C(SpatialCoordinates d, ℝ)] [_portFact : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)] (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (i j : Fin d) :
    ∃ hmem : ∀ _K : ℕ, MemLp (fun _ : BilateralField d => if i = j then (1 : ℝ) else (0 : ℝ)) 1
        (chaosSampleLaw M).toMeasure,
      IsCompact (closure (Set.range (fun K =>
        (hmem K).toLp (fun _ : BilateralField d => if i = j then (1 : ℝ) else (0 : ℝ))))) := by
  have hmem : ∀ K : ℕ, MemLp (fun _ : BilateralField d => if i = j then (1 : ℝ) else (0 : ℝ)) 1
      (chaosSampleLaw M).toMeasure := fun _ => memLp_const _
  refine ⟨hmem, ?_⟩
  have hconst : (fun K => (hmem K).toLp (fun _ : BilateralField d =>
      if i = j then (1 : ℝ) else (0 : ℝ))) =
      fun _ => (hmem 0).toLp (fun _ : BilateralField d => if i = j then (1 : ℝ) else (0 : ℝ)) := by
    funext K
    exact MemLp.toLp_congr (hmem K) (hmem 0) (Filter.EventuallyEq.refl _ _)
  have hrange : Set.range (fun _ : ℕ => (hmem 0).toLp (fun _ : BilateralField d =>
      if i = j then (1 : ℝ) else (0 : ℝ))) =
      {(hmem 0).toLp (fun _ : BilateralField d => if i = j then (1 : ℝ) else (0 : ℝ))} :=
    Set.range_const
  rw [hconst, hrange, closure_singleton]
  exact isCompact_singleton

/-- The `sigmaStarInvCoarse (i,j)` entry compactness, any `(i,j)`, CONDITIONAL on
`NeumannResponseCompactAtOrigin` (see `g9_sigma_entries_compact.lean`'s own docstring for exactly
what remains open). -/
theorem aux_g9_probemax_entries_compact_starinv_entry
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

/-- Paper `mfd:sec-local-form` (Section 9), the `paperScalarProbeMax` half of the cell matrix
family in `lem_prefix_limit_g9_cell_compact`, at the unit root cell only: for the identity chart
on the origin cube, the normalized scalar probe `P(R;F,1)` is, as a family over the cutoff `K`,
integrable and relatively compact in `L¹`, CONDITIONAL on `NeumannResponseCompactAtOrigin` (the
same standing Neumann gap as `g9_sigma_entries_compact`/`g9_matrixnorm_entries_compact`). Reduces
`paperScalarProbeMax` at `alpha = 1` to `matrixNorm((1/2)(sigmaCoarse + sigmaStarInvCoarse) - 1)`
via `kappaCoarse = 0` (`responseSymmetricDirichletNeumannTheory`) and
`paperScalarProbeMaxOn_eq_ofReal_matrixOperatorNorm` -- no matrix-inversion-continuity argument is
needed, since the reduction is already linear in the two already-compact entry families plus a
fixed identity indicator -- then transports entrywise `L¹` compactness through this combination via
`isCompact_closure_range_lipschitz_combo`. -/
theorem g9_probemax_entries_compact
    (hNeumann : NeumannResponseCompactAtOrigin d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (D : @_root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d ⟨by omega⟩) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ min 1 delta0 →
        ∃ hmem : ∀ K, MemLp (fun omega => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax
            (Homogenization.originCube d 0) (aux_g9_probemax_entries_compact_F Jc M H omega K) 1).toReal) 1
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (fun omega =>
          (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax (Homogenization.originCube d 0)
            (aux_g9_probemax_entries_compact_F Jc M H omega K) 1).toReal)))) := by
  have hentry : ∀ p : Fin d × Fin d × Fin 3,
      ∃ delta1 : ℝ, 0 < delta1 ∧
        ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
          (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H),
          M.delta ≤ min 1 delta1 →
          ∃ hmem : ∀ K, MemLp (fun omega => aux_g9_probemax_entries_compact_triple Jc M H p K omega) 1
            (chaosSampleLaw M).toMeasure,
          IsCompact (closure (Set.range (fun K => (hmem K).toLp
            (fun omega => aux_g9_probemax_entries_compact_triple Jc M H p K omega)))) := by
    rintro ⟨i, j, k⟩
    by_cases hk0 : k = 0
    · subst hk0
      obtain ⟨delta1, hpos, hall⟩ := g9_sigma_entries_compact hd Jc Pc Xc W Sf D i j
      refine ⟨delta1, hpos, ?_⟩
      intro M Rm Sreg It H hH hM
      obtain ⟨hmem, hcompact⟩ := hall M Rm Sreg It H hH hM
      have heqfun : (fun (K : ℕ) (omega : BilateralField d) =>
          aux_g9_probemax_entries_compact_triple Jc M H (i, j, 0) K omega) =
          (fun K omega => Book.Ch02.sigmaCoarse (cubeDomain (Homogenization.originCube d 0))
            (aux_g9_sigma_entries_compact_A Jc M H omega K) i j) := by
        funext K omega
        exact aux_g9_probemax_entries_compact_triple_zero Jc M H i j K omega
      have hmem1 : ∀ K, MemLp (fun omega =>
          aux_g9_probemax_entries_compact_triple Jc M H (i, j, 0) K omega) 1
          (chaosSampleLaw M).toMeasure := by
        intro K
        rw [congrFun heqfun K]
        exact hmem K
      refine ⟨hmem1, ?_⟩
      have hrep : (fun K => (hmem1 K).toLp (fun omega =>
          aux_g9_probemax_entries_compact_triple Jc M H (i, j, 0) K omega)) =
          (fun K => (hmem K).toLp (fun omega => Book.Ch02.sigmaCoarse
            (cubeDomain (Homogenization.originCube d 0))
            (aux_g9_sigma_entries_compact_A Jc M H omega K) i j)) := by
        funext K
        exact MemLp.toLp_congr (hmem1 K) (hmem K) (Filter.EventuallyEq.of_eq (congrFun heqfun K))
      rw [hrep]
      exact hcompact
    · by_cases hk1 : k = 1
      · subst hk1
        obtain ⟨delta1, hpos, hall⟩ := aux_g9_probemax_entries_compact_starinv_entry hNeumann Jc i j
        refine ⟨delta1, hpos, ?_⟩
        intro M Rm Sreg It H hH hM
        obtain ⟨hmem, hcompact⟩ := hall M Rm Sreg H hH hM
        have heqfun : (fun (K : ℕ) (omega : BilateralField d) =>
            aux_g9_probemax_entries_compact_triple Jc M H (i, j, 1) K omega) =
            (fun K omega => Book.Ch02.sigmaStarInvCoarse (cubeDomain (Homogenization.originCube d 0))
              (aux_g9_sigma_entries_compact_A Jc M H omega K) i j) := by
          funext K omega
          exact aux_g9_probemax_entries_compact_triple_one Jc M H i j K omega
        have hmem1 : ∀ K, MemLp (fun omega =>
            aux_g9_probemax_entries_compact_triple Jc M H (i, j, 1) K omega) 1
            (chaosSampleLaw M).toMeasure := by
          intro K
          rw [congrFun heqfun K]
          exact hmem K
        refine ⟨hmem1, ?_⟩
        have hrep : (fun K => (hmem1 K).toLp (fun omega =>
            aux_g9_probemax_entries_compact_triple Jc M H (i, j, 1) K omega)) =
            (fun K => (hmem K).toLp (fun omega => Book.Ch02.sigmaStarInvCoarse
              (cubeDomain (Homogenization.originCube d 0))
              (aux_g9_sigma_entries_compact_A Jc M H omega K) i j)) := by
          funext K
          exact MemLp.toLp_congr (hmem1 K) (hmem K) (Filter.EventuallyEq.of_eq (congrFun heqfun K))
        rw [hrep]
        exact hcompact
      · have hk2 : k = 2 := by omega
        subst hk2
        refine ⟨1, one_pos, ?_⟩
        intro M Rm Sreg It H hH _
        obtain ⟨hmem, hcompact⟩ := aux_g9_probemax_entries_compact_const_compact M i j
        have heqfun : (fun (K : ℕ) (omega : BilateralField d) =>
            aux_g9_probemax_entries_compact_triple Jc M H (i, j, 2) K omega) =
            (fun K _ => if i = j then (1 : ℝ) else (0 : ℝ)) := by
          funext K omega
          exact aux_g9_probemax_entries_compact_triple_two Jc M H i j K omega
        have hmem1 : ∀ K, MemLp (fun omega =>
            aux_g9_probemax_entries_compact_triple Jc M H (i, j, 2) K omega) 1
            (chaosSampleLaw M).toMeasure := by
          intro K
          rw [congrFun heqfun K]
          exact hmem K
        refine ⟨hmem1, ?_⟩
        have hrep : (fun K => (hmem1 K).toLp (fun omega =>
            aux_g9_probemax_entries_compact_triple Jc M H (i, j, 2) K omega)) =
            (fun K => (hmem K).toLp (fun _ : BilateralField d => if i = j then (1 : ℝ) else (0 : ℝ))) := by
          funext K
          exact MemLp.toLp_congr (hmem1 K) (hmem K) (Filter.EventuallyEq.of_eq (congrFun heqfun K))
        rw [hrep]
        exact hcompact
  choose delta1 hdelta1pos hall using hentry
  have hne : (Finset.univ : Finset (Fin d × Fin d × Fin 3)).Nonempty := Finset.univ_nonempty
  refine ⟨Finset.univ.inf' hne delta1, (Finset.lt_inf'_iff hne).mpr (fun p _ => hdelta1pos p), ?_⟩
  intro M Rm Sreg It H hH hM
  have hMp : ∀ p : Fin d × Fin d × Fin 3, M.delta ≤ min 1 (delta1 p) := by
    intro p
    refine hM.trans (min_le_min_left 1 ?_)
    exact Finset.inf'_le delta1 (Finset.mem_univ p)
  have hallM : ∀ p : Fin d × Fin d × Fin 3,
      ∃ hmem : ∀ K, MemLp (fun omega => aux_g9_probemax_entries_compact_triple Jc M H p K omega) 1
        (chaosSampleLaw M).toMeasure,
      IsCompact (closure (Set.range (fun K => (hmem K).toLp
        (fun omega => aux_g9_probemax_entries_compact_triple Jc M H p K omega)))) :=
    fun p => hall p M Rm Sreg It H hH (hMp p)
  choose hmemEntry hcompactEntry using hallM
  obtain ⟨hcombMem, hcombCompact⟩ := isCompact_closure_range_lipschitz_combo
    (f := fun p K omega => aux_g9_probemax_entries_compact_triple Jc M H p K omega)
    (hmem := hmemEntry) (hf := hcompactEntry)
    (g := aux_g9_probemax_entries_compact_g d) (c := (Fintype.card (Fin d) : ℝ))
    (hc := by positivity) (hg0 := aux_g9_probemax_entries_compact_g0 d)
    (hglip := aux_g9_probemax_entries_compact_glip d)
  have heqfun : (fun (K : ℕ) (omega : BilateralField d) =>
      (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax (Homogenization.originCube d 0)
        (aux_g9_probemax_entries_compact_F Jc M H omega K) 1).toReal) =
      (fun K omega => aux_g9_probemax_entries_compact_g d
        (fun p => aux_g9_probemax_entries_compact_triple Jc M H p K omega)) := by
    funext K omega
    exact aux_g9_probemax_entries_compact_triple_eq Jc M H omega K
  have hmem1 : ∀ K, MemLp (fun omega => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax
      (Homogenization.originCube d 0) (aux_g9_probemax_entries_compact_F Jc M H omega K) 1).toReal) 1
      (chaosSampleLaw M).toMeasure := by
    intro K
    rw [congrFun heqfun K]
    exact hcombMem K
  refine ⟨hmem1, ?_⟩
  have hrep : (fun K => (hmem1 K).toLp (fun omega => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax
      (Homogenization.originCube d 0) (aux_g9_probemax_entries_compact_F Jc M H omega K) 1).toReal)) =
      (fun K => (hcombMem K).toLp (fun omega => aux_g9_probemax_entries_compact_g d
        (fun p => aux_g9_probemax_entries_compact_triple Jc M H p K omega))) := by
    funext K
    exact MemLp.toLp_congr (hmem1 K) (hcombMem K) (Filter.EventuallyEq.of_eq (congrFun heqfun K))
  rw [hrep]
  exact hcombCompact

end SubdiffusiveProcess.Paper
