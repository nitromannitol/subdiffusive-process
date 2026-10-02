import SubdiffusiveProcess.Analysis.ScalarProbeMaxReduction
import SubdiffusiveProcess.Paper.chart_coords_measurable
import SubdiffusiveProcess.Paper.lem_extension_cell_moment

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess SubdiffusiveProcess.Lane4 Homogenization Set
open TopologicalSpace Homogenization.Book.Ch02
open scoped ENNReal NNReal

noncomputable section
namespace Paper

variable {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)]

/-- General-`R` mirror of `g9_sigma_entries_compact`'s `aux_bridge1_scalar_ae`: the identity
chart's coefficient on ANY sub-cube `R ⊆` the origin cube agrees a.e. with the raw scalar field
(mirrors `aux_lem_extension_cell_moment_chart_scalar_identity`'s own generality, already parametric
in the target cube). -/
theorem aux_probemax_measurable_R_gen_scalar_ae (I : Paper.in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (K : ℕ) (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    ((I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1).coeffOn R).toCoeffField
      =ᵐ[volumeMeasureOn (Homogenization.openCubeSet R)]
      fun x => Homogenization.scalarMatrix (cutoffCoefficient M H omega K x) := by
  have h := aux_lem_extension_cell_moment_chart_scalar_identity I M H omega K
    (0 : SpatialCoordinates d) 1 one_pos (0 : SpatialCoordinates d) 1 one_pos subset_rfl R hR
  filter_upwards [h] with x hx
  have hfeq : (fun i => (0 : SpatialCoordinates d) i + 1 * x i) = x := by funext i; simp
  rw [hx, hfeq]

/-- General-`R` mirror of `aux_g9_sigma_entries_compact_symm`: the identity chart's coefficient
is symmetric on any sub-cube `R` of the origin cube. -/
theorem aux_probemax_measurable_R_gen_symm (I : Paper.in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (K : ℕ) (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    CoeffOn.IsSymmetric
      ((I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1).coeffOn R) := by
  filter_upwards [aux_probemax_measurable_R_gen_scalar_ae I M H omega K R hR] with x hx
  rw [hx]
  exact Homogenization.scalarMatrix_isSymm _

/-- The `(sigma, sigmaStarInv, identity)` triple at cell `R`, index `(i,j,k)`, `k = 0/1/2`. -/
def aux_probemax_measurable_R_gen_triple (I : Paper.in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (R : Homogenization.TriadicCube d) (p : Fin d × Fin d × Fin 3) (K : ℕ)
    (omega : BilateralField d) : ℝ :=
  if p.2.2 = 0 then
    Book.Ch02.sigmaCoarse (cubeDomain R)
      ((I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1).coeffOn R) p.1 p.2.1
  else if p.2.2 = 1 then
    Book.Ch02.sigmaStarInvCoarse (cubeDomain R)
      ((I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1).coeffOn R) p.1 p.2.1
  else if p.1 = p.2.1 then (1 : ℝ) else (0 : ℝ)

/-- `paperScalarProbeMax` at a general cell `R`, reduced to `probeMaxReduction_g`
applied to the triple -- the general-`R` mirror of `aux_g9_probemax_entries_compact_triple_eq`
(`g9_probemax_entries_compact`, origin cube only). -/
theorem aux_probemax_measurable_R_gen_triple_eq (I : Paper.in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (K : ℕ) (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
        (I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1) 1).toReal =
      probeMaxReduction_g d
        (fun p => aux_probemax_measurable_R_gen_triple I M H R p K omega) := by
  have hsym := aux_probemax_measurable_R_gen_symm I M H omega K R hR
  rw [probeMaxReduction_toReal R
    (I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1) hsym]
  unfold probeMaxReduction_R probeMaxReduction_g
  congr 1
  funext i j
  have h10 : ¬ (1 : Fin 3) = 0 := by decide
  have h20 : ¬ (2 : Fin 3) = 0 := by decide
  have h21 : ¬ (2 : Fin 3) = 1 := by decide
  simp only [aux_probemax_measurable_R_gen_triple, if_true, if_neg h10, if_neg h20, if_neg h21,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, if_true]
    ring
  · simp only [Matrix.one_apply_ne hij, if_neg hij]
    ring

/-- Each entry of the triple is `Measurable` in `omega`, at any cell `R ⊆` the origin cube. Reduces
`sigmaCoarse`'s measurability to `bCoarse`'s (`aux_core_bCoarse_measurable_R_gen`, already general
in `R`) via the symmetric-coefficient identity `aux_core_sigmaCoarse_eq_bCoarse_R`; `sigmaStarInv`
is already general in `R` directly (`aux_core_sigmaStarInvCoarse_measurable_R_gen`). Both from
`chart_coords_measurable`. -/
theorem aux_probemax_measurable_R_gen_triple_measurable (hd : 2 ≤ d) (I : Paper.in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHm : Measurable H) (K : ℕ) (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0))
    (p : Fin d × Fin d × Fin 3) :
    Measurable (fun omega => aux_probemax_measurable_R_gen_triple I M H R p K omega) := by
  rcases p with ⟨i, j, k⟩
  by_cases hk0 : k = 0
  · subst hk0
    have heq : (fun omega => aux_probemax_measurable_R_gen_triple I M H R (i, j, 0) K omega) =
        (fun omega => Book.Ch02.sigmaCoarse (cubeDomain R)
          ((I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1).coeffOn R) i j) := by
      funext omega; simp [aux_probemax_measurable_R_gen_triple]
    rw [heq]
    have hbeq : ∀ omega, Book.Ch02.sigmaCoarse (cubeDomain R)
        ((I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1).coeffOn R) i j =
        Book.Ch02.bCoarse (cubeDomain R)
        ((I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1).coeffOn R) i j := by
      intro omega
      have := aux_core_sigmaCoarse_eq_bCoarse_R hd I (0 : SpatialCoordinates d) 1 one_pos
        (cutoffPositiveCoefficient M H omega K 0 one_pos) R hR
      exact congrFun (congrFun this i) j
    simp_rw [hbeq]
    exact aux_core_bCoarse_measurable_R_gen hd I M H hHm K 0 1 one_pos R hR i j
  · by_cases hk1 : k = 1
    · subst hk1
      have heq : (fun omega => aux_probemax_measurable_R_gen_triple I M H R (i, j, 1) K omega) =
          (fun omega => Book.Ch02.sigmaStarInvCoarse (cubeDomain R)
            ((I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1).coeffOn R) i j) := by
        funext omega; simp [aux_probemax_measurable_R_gen_triple]
      rw [heq]
      exact aux_core_sigmaStarInvCoarse_measurable_R_gen hd I M H hHm K 0 1 one_pos R hR i j
    · have hk2 : k = 2 := by omega
      subst hk2
      have heq : (fun omega => aux_probemax_measurable_R_gen_triple I M H R (i, j, 2) K omega) =
          (fun _ : BilateralField d => if i = j then (1 : ℝ) else (0 : ℝ)) := by
        funext omega
        have h20 : ¬ (2 : Fin 3) = 0 := by decide
        have h21 : ¬ (2 : Fin 3) = 1 := by decide
        simp only [aux_probemax_measurable_R_gen_triple, if_neg h20, if_neg h21]
      rw [heq]
      exact measurable_const

/-- Paper `mfd:sec-local-form` (Section 9), a Lean-only infrastructure fact for
`lem_prefix_limit`'s response-moment bank (`aux_lem_prefix_limit_response_moments`, its `I.err`
coordinate): `paperScalarProbeMax R (F K omega) 1` is `Measurable` in `omega`, at ANY triadic
cell `R` inside the origin cube -- not just at `R = ` the origin cube itself, which is all
`g9_probemax_entries_compact` supplies. This was the exact missing "item 2" measurability gap
recorded in `lem_prefix_limit_err_moment_bank/RECEIPT.md`: `I.err`'s value is a geometric-weighted
supremum over MANY descendant cells (via `SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite`
and `paperScaleResponseAtScale`), so the origin-only measurability is insufficient. -/
theorem probemax_measurable_R_gen (hd : 2 ≤ d) (I : Paper.in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHm : Measurable H) (K : ℕ) (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    Measurable (fun omega : BilateralField d =>
      (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
        (I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1) 1).toReal) := by
  have heq : (fun omega => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
        (I.chart 0 1 one_pos (cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1) 1).toReal) =
      (fun omega => probeMaxReduction_g d
        (fun p => aux_probemax_measurable_R_gen_triple I M H R p K omega)) := by
    funext omega
    exact aux_probemax_measurable_R_gen_triple_eq I M H omega K R hR
  rw [heq]
  have hcont : Continuous (probeMaxReduction_g d) :=
    lipCombo_continuous (probeMaxReduction_g d) (Fintype.card (Fin d) : ℝ)
      (by positivity) (probeMaxReduction_glip d)
  exact hcont.measurable.comp (measurable_pi_lambda _
    (fun p => aux_probemax_measurable_R_gen_triple_measurable hd I M H hHm K R hR p))

end Paper
