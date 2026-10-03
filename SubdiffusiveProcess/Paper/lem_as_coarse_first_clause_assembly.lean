module

public import SubdiffusiveProcess.Paper.lem_as_coarse_multiscale_assembly
public import SubdiffusiveProcess.Paper.lem_extension_cell_moment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.OneCubeEllipticityComparison
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import Homogenization.Book.Ch02.Theorems.MatrixPositivity
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane4.Bridge
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import Mathlib.Tactic

@[expose] public section




set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

section SegSubwave
/-!
# `lem_as_coarse`: multiscale assembly, part 2 (below the last wavelength)

Paper lines 4546--4549: "Below the last wavelength it is at most
`C3^{-sN}(sup_Q A_N + sup_Q A_N^{-1})`."  The cell-matrix input for that sentence:
a pointwise bound `lo ≤ a ≤ hi` of the scalar coefficient gives, on every triadic cell of the
chart, `|b(Q)| ≤ hi` and `|σ_*⁻¹(Q)| ≤ lo⁻¹` (sharp: the upper matrix is below the arithmetic
mean, the inverse lower matrix below the harmonic mean, `e.ord.bounds.truncated`).
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory
open Homogenization.Book.Ch02
open SubdiffusiveProcess SubdiffusiveProcess.Lane4


namespace Paper

/-- Normalized average of an a.e. bounded function. -/
theorem aux_lem_as_coarse_ms_average_le {d : ℕ} (U : Domain d)
    (f : Homogenization.Vec d → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hfin : volume (U : Set (Homogenization.Vec d)) ≠ ⊤)
    (hf : ∀ᵐ x ∂volume.restrict (U : Set (Homogenization.Vec d)), f x ≤ c) :
    Homogenization.Book.Ch02.average U f ≤ c := by
  unfold Homogenization.Book.Ch02.average
  set V : ℝ := (volume (U : Set (Homogenization.Vec d))).toReal with hVdef
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  by_cases hint : Integrable f (volume.restrict (U : Set (Homogenization.Vec d)))
  · haveI : IsFiniteMeasure (volume.restrict (U : Set (Homogenization.Vec d))) :=
      isFiniteMeasure_restrict.mpr hfin
    have h1 : ∫ x in (U : Set (Homogenization.Vec d)), f x ≤
        ∫ _x in (U : Set (Homogenization.Vec d)), c :=
      integral_mono_ae hint (integrable_const c) hf
    rw [setIntegral_const, smul_eq_mul, Measure.real] at h1
    rw [← hVdef] at h1
    rcases hV0.eq_or_lt with h | h
    · rw [← h, inv_zero, zero_mul]; exact hc
    · calc V⁻¹ * ∫ x in (U : Set (Homogenization.Vec d)), f x ≤ V⁻¹ * (V * c) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hV0)
        _ = c := by field_simp
  · rw [integral_undef hint, mul_zero]; exact hc

/-- The average of an a.e. scalar matrix field is the scalar matrix of the average. -/
theorem aux_lem_as_coarse_ms_averageMat_scalar {d : ℕ} (U : Domain d)
    (A : Homogenization.Vec d → Homogenization.Mat d) (f : Homogenization.Vec d → ℝ)
    (hA : ∀ᵐ x ∂volume.restrict (U : Set (Homogenization.Vec d)),
      A x = Homogenization.scalarMatrix (f x)) :
    averageMat U A = Homogenization.scalarMatrix (Homogenization.Book.Ch02.average U f) := by
  ext i j
  unfold averageMat Homogenization.Book.Ch02.average
  rw [integral_congr_ae (hA.mono fun x hx => by rw [hx])]
  by_cases hij : i = j
  · subst hij; simp [Homogenization.scalarMatrix]
  · simp [Homogenization.scalarMatrix, hij]

theorem aux_lem_as_coarse_ms_vecDot_scalar {d : ℕ} (t : ℝ) (e : Homogenization.Vec d) :
    Homogenization.vecDot e
        (Homogenization.matVecMul (Homogenization.scalarMatrix (d := d) t) e) =
      t * Homogenization.vecNormSq e := by
  rw [Homogenization.matVecMul_scalarMatrix, Homogenization.vecDot_smul_right]
  rfl

theorem aux_lem_as_coarse_ms_symmPart_scalar {d : ℕ} (t : ℝ) :
    Homogenization.symmPart (Homogenization.scalarMatrix (d := d) t) =
      Homogenization.scalarMatrix t := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Homogenization.symmPart, Homogenization.scalarMatrix]
  · have hji : j ≠ i := Ne.symm hij
    simp [Homogenization.symmPart, Homogenization.scalarMatrix, hij, hji]

theorem aux_lem_as_coarse_ms_inv_scalar {d : ℕ} {t : ℝ} (ht : t ≠ 0) :
    (Homogenization.scalarMatrix (d := d) t)⁻¹ = Homogenization.scalarMatrix t⁻¹ := by
  rw [Homogenization.scalarMatrix, Homogenization.nonsing_inv_smul t ht (by simp)]
  simp [Homogenization.scalarMatrix]

/-- **Sharp one-cell envelope.**  If a Ch02 coefficient is a.e. the scalar field `f` with
`lo ≤ f ≤ hi`, then `|b(U)| ≤ hi` and `|σ_*⁻¹(U)| ≤ lo⁻¹`. -/
theorem aux_lem_as_coarse_ms_cell_norms_le_of_scalar {d : ℕ} [NeZero d] (Jc : in_J d)
    (U : Domain d) (a : CoeffOn U) (f : Homogenization.Vec d → ℝ) {lo hi : ℝ}
    (hlo : 0 < lo) (hle : lo ≤ hi)
    (hfin : volume (U : Set (Homogenization.Vec d)) ≠ ⊤)
    (ha : ∀ᵐ x ∂volume.restrict (U : Set (Homogenization.Vec d)),
      a.toCoeffField x = Homogenization.scalarMatrix (f x))
    (hf : ∀ᵐ x ∂volume.restrict (U : Set (Homogenization.Vec d)), lo ≤ f x ∧ f x ≤ hi) :
    matrixNorm (bCoarse U a) ≤ hi ∧ matrixNorm (sigmaStarInvCoarse U a) ≤ lo⁻¹ := by
  have hsym : CoeffOn.IsSymmetric a :=
    ha.mono fun x hx => by rw [hx]; exact Homogenization.scalarMatrix_isSymm _
  have hT := responseSymmetricDirichletNeumannTheory U a hsym
  have hhi : 0 ≤ hi := le_trans hlo.le hle
  constructor
  · have havg : averageMat U a.toCoeffField = Homogenization.scalarMatrix (Homogenization.Book.Ch02.average U f) :=
      aux_lem_as_coarse_ms_averageMat_scalar U _ f ha
    have hmean : Homogenization.Book.Ch02.average U f ≤ hi :=
      aux_lem_as_coarse_ms_average_le U f hhi hfin (hf.mono fun x hx => hx.2)
    refine SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.matrixNorm_le_of_forall_unit
      (bCoarse_posSemidef U a) hhi ?_
    intro e he
    have hbr := hT.dirichlet_neumann_bracketing.2.2 e
    rw [havg, aux_lem_as_coarse_ms_vecDot_scalar, he] at hbr
    rw [hT.derived_matrices.2.2]
    linarith
  · have hinv : ∀ᵐ x ∂volume.restrict (U : Set (Homogenization.Vec d)),
        (Homogenization.symmPart (a.toCoeffField x))⁻¹ =
          Homogenization.scalarMatrix (f x)⁻¹ := by
      filter_upwards [ha, hf] with x hx hfx
      rw [hx, aux_lem_as_coarse_ms_symmPart_scalar,
        aux_lem_as_coarse_ms_inv_scalar (ne_of_gt (lt_of_lt_of_le hlo hfx.1))]
    have havg : averagedSymmPartInv U a =
        Homogenization.scalarMatrix (Homogenization.Book.Ch02.average U fun x => (f x)⁻¹) :=
      aux_lem_as_coarse_ms_averageMat_scalar U _ _ hinv
    have hmean : Homogenization.Book.Ch02.average U (fun x => (f x)⁻¹) ≤ lo⁻¹ :=
      aux_lem_as_coarse_ms_average_le U _ (inv_nonneg.2 hlo.le) hfin
        (hf.mono fun x hx => inv_anti₀ hlo hx.1)
    refine SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.matrixNorm_le_of_forall_unit
      (sigmaStarInvCoarse_posDef U a).posSemidef (inv_nonneg.2 hlo.le) ?_
    intro e he
    have hob := (Jc.ord_bounds U a hsym e).1
    rw [havg, aux_lem_as_coarse_ms_vecDot_scalar, he] at hob
    linarith

/-- Open triadic cubes have finite volume. -/
theorem aux_lem_as_coarse_ms_volume_cube_ne_top {d : ℕ} (Q : Homogenization.TriadicCube d) :
    volume (Homogenization.openCubeSet Q) ≠ ⊤ := by
  rw [← Homogenization.ball_cubeCenter_eq_openCubeSet]
  exact measure_ball_lt_top.ne

/-- The chart `x ↦ w + r' x` sends the unit root into the cell `centeredCube w r'`. -/
theorem aux_lem_as_coarse_ms_affine_mem {d : ℕ} (w : SpatialCoordinates d)
    (r' : ℝ) (hr' : 0 < r') {x : SpatialCoordinates d}
    (hx : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    (fun i => w i + r' * x i) ∈ (centeredCube w r' hr' : Set (SpatialCoordinates d)) := by
  rw [centeredCube_eq_pi]
  have hx' : ∀ i, -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2 := by
    simpa [Homogenization.openCubeSet, Homogenization.originCube,
      Homogenization.cubeScaleFactor] using hx
  intro i _
  have h1 := mul_lt_mul_of_pos_left (hx' i).1 hr'
  have h2 := mul_lt_mul_of_pos_left (hx' i).2 hr'
  constructor <;> linarith

theorem aux_lem_as_coarse_ms_qmp_affine {d : ℕ} (w : SpatialCoordinates d)
    (r' : ℝ) (hr' : 0 < r') :
    Measure.QuasiMeasurePreserving (fun x : SpatialCoordinates d => fun i => w i + r' * x i)
      volume volume := by
  have h1 : Measure.QuasiMeasurePreserving (fun y : SpatialCoordinates d => r' • y)
      volume volume :=
    Measure.quasiMeasurePreserving_smul volume hr'.ne'
  have h2 : Measure.QuasiMeasurePreserving (fun y : SpatialCoordinates d => y + w)
      volume volume :=
    (measurePreserving_add_right volume w).quasiMeasurePreserving
  have heq : (fun x : SpatialCoordinates d => fun i => w i + r' * x i) =
      (fun y : SpatialCoordinates d => y + w) ∘ (fun y : SpatialCoordinates d => r' • y) := by
    funext x i
    simp [add_comm]
  rw [heq]
  exact h2.comp h1

/-- **Chart envelope below the wavelength.**  An a.e. bound `lo ≤ a ≤ hi` on the root cube
bounds both cell matrices of every triadic cell of every contained chart. -/
theorem aux_lem_as_coarse_ms_chart_norms_le {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi)
    (hbd : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      lo ≤ a.val y ∧ a.val y ≤ hi)
    (Q : Homogenization.TriadicCube d)
    (hQ : Homogenization.openCubeSet Q ⊆
      Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    coarseBMatrixNorm Q (Jc.chart z r hr a w r') ≤ hi ∧
      coarseSigmaStarInvMatrixNorm Q (Jc.chart z r hr a w r') ≤ lo⁻¹ := by
  haveI : NeZero d := ⟨by omega⟩
  have hc := Jc.chart_eq z r hr a w r' hr' hsub Q hQ
  have hQmeas := Homogenization.measurableSet_openCubeSet Q
  have hmaps : ∀ x ∈ Homogenization.openCubeSet Q,
      (fun i => w i + r' * x i) ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    fun x hx => hsub (aux_lem_as_coarse_ms_affine_mem w r' hr' (hQ hx))
  have hpull : ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet Q),
      lo ≤ a.val (fun i => w i + r' * x i) ∧ a.val (fun i => w i + r' * x i) ≤ hi := by
    rw [ae_restrict_iff' (centeredCube z r hr).isOpen.measurableSet] at hbd
    rw [ae_restrict_iff' hQmeas]
    filter_upwards [(aux_lem_as_coarse_ms_qmp_affine w r' hr').ae hbd] with x hx hxQ
    exact hx (hmaps x hxQ)
  exact aux_lem_as_coarse_ms_cell_norms_le_of_scalar Jc (cubeDomain Q)
    ((Jc.chart z r hr a w r').coeffOn Q) (fun x => a.val (fun i => w i + r' * x i))
    hlo hle (aux_lem_as_coarse_ms_volume_cube_ne_top Q) hc hpull

/-- The cutoff coefficient's `L^∞` class is a.e. the continuous field `A_N` on the root, so a
pointwise envelope of `A_N` on the root is an a.e. envelope of the carried coefficient. -/
theorem aux_lem_as_coarse_ms_cutoff_ae_bounds {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) {lo hi : ℝ}
    (hbd : ∀ y ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      lo ≤ cutoffCoefficient M H om N y ∧ cutoffCoefficient M H om N y ≤ hi) :
    ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      lo ≤ (cutoffPositiveCoefficient M H om N z hr).val y ∧
        (cutoffPositiveCoefficient M H om N z hr).val y ≤ hi := by
  haveI : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (closedCube z r hr : Set (SpatialCoordinates d))) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have h0 := normalizedContinuousPositiveCoefficient_coeFn
    (Ω := centeredCube z r hr) (closedCube z r hr)
    (cutoffCoefficientCM M H om N z hr) (cutoffCoefficientCM_pos M H om N z hr) 1 one_pos
  filter_upwards [h0, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet]
    with y hy hyQ
  have hval := hy hyQ
  rw [div_one] at hval
  change lo ≤ (cutoffPositiveCoefficient M H om N z hr).val y ∧
    (cutoffPositiveCoefficient M H om N z hr).val y ≤ hi
  unfold cutoffPositiveCoefficient
  rw [hval]
  exact hbd y hyQ

end Paper

end SegSubwave

section SegTransport
/-!
# `lem_as_coarse`: multiscale assembly, part 3 (grid-cell charts ↔ root-chart cells)

A grid cell `w + r' Q₀` of the root has its own `in_J` chart; the paper's cell matrices
`a(q;A_N)`, `a_*⁻¹(q;A_N)` are read there (that is how `lem_extension`'s grid clause and the
shifted response bank see them).  `Λ_{s,q}` of the root, however, sums the matrices of the
triadic descendants `R` of the unit root in the **root** chart.  This part proves that the two
readings coincide: every Ch02 coarse matrix is an explicit function of the response functional
`J`, and `J` is invariant under the translation and dilation carrying `R` onto `Q₀`
(`aux_lem_extension_cell_moment_reference_on_cube`).
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory
open Homogenization.Book.Ch02
open SubdiffusiveProcess SubdiffusiveProcess.Lane4


namespace Paper

/-- Every Ch02 coarse matrix is a function of the response functional alone. -/
theorem aux_lem_as_coarse_ms_coarse_congr {d : ℕ} {U V : Domain d} {a : CoeffOn U}
    {b : CoeffOn V} (h : ∀ p q, responseJ U a p q = responseJ V b p q) :
    bCoarse U a = bCoarse V b ∧ sigmaStarInvCoarse U a = sigmaStarInvCoarse V b := by
  have hS : sigmaStarInvCoarse U a = sigmaStarInvCoarse V b := by
    funext i j
    simp only [sigmaStarInvCoarse, sigmaStarInvEntry, h]
  have hSK : sigmaStarInvKappaCoarse U a = sigmaStarInvKappaCoarse V b := by
    funext i j
    simp only [sigmaStarInvKappaCoarse, mixedResponse, h]
  have hK : kappaCoarse U a = kappaCoarse V b := by
    simp only [kappaCoarse, sigmaStarCoarse, hS, hSK]
  have hC : ∀ p, canonicalSigmaCorrectedResponse U a p = canonicalSigmaCorrectedResponse V b p := by
    intro p
    simp only [canonicalSigmaCorrectedResponse, hK, hS, h]
  have hsig : sigmaCoarse U a = sigmaCoarse V b := by
    funext i j
    simp only [sigmaCoarse, sigmaEntry, hC]
  refine ⟨?_, hS⟩
  simp only [bCoarse, coarseMatrices, CoarseMatrices.b, hsig, hS, hK]

/-- The depth-`n` descendants of the unit root have scale `-n`. -/
theorem aux_lem_as_coarse_ms_desc_scale {d n : ℕ} {R : Homogenization.TriadicCube d}
    (hR : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (n : ℤ))) :
    R.scale = -(n : ℤ) := by
  have := Homogenization.scale_eq_of_mem_descendantsAtScale hR
  simpa [Homogenization.originCube] using this

theorem aux_lem_as_coarse_ms_desc_sub {d n : ℕ} {R : Homogenization.TriadicCube d}
    (hR : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (n : ℤ))) :
    Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) :=
  Homogenization.openCubeSet_subset_of_mem_descendantsAtScale
    (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) hR

/-- The physical centre `z + r 3^{-n} v` of the grid cell carried by a depth-`n` descendant
with index `v`; this is the child statements' `fun i => z i + r * 3^{-k} * n i`. -/
def aux_lem_as_coarse_ms_cellCenter {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (n : ℕ)
    (v : Fin d → ℤ) : SpatialCoordinates d :=
  fun i => z i + r * (3 : ℝ) ^ (-(n : ℤ)) * (v i : ℝ)

/-- The grid cell of a descendant lies in the root. -/
theorem aux_lem_as_coarse_ms_cell_sub {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (n : ℕ) {R : Homogenization.TriadicCube d}
    (hR : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (n : ℤ)))
    (hr' : 0 < r * (3 : ℝ) ^ (-(n : ℤ))) :
    (centeredCube (aux_lem_as_coarse_ms_cellCenter z r n R.index) (r * (3 : ℝ) ^ (-(n : ℤ))) hr' :
      Set (SpatialCoordinates d)) ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  intro y hy
  rw [centeredCube_eq_pi] at hy ⊢
  have hscale := aux_lem_as_coarse_ms_desc_scale hR
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(n : ℤ)) := by positivity
  let x : SpatialCoordinates d := fun i => (y i - z i) / r
  have hxR : x ∈ Homogenization.openCubeSet R := by
    intro i
    have hyi := hy i (Set.mem_univ i)
    simp only [aux_lem_as_coarse_ms_cellCenter, Set.mem_Ioo] at hyi
    simp only [Homogenization.cubeScaleFactor, hscale, x]
    constructor
    · rw [lt_div_iff₀ hr]; nlinarith [hyi.1]
    · rw [div_lt_iff₀ hr]; nlinarith [hyi.2]
  have hx0 := aux_lem_as_coarse_ms_desc_sub hR hxR
  intro i _
  have hxi := (Homogenization.mem_openCubeSet_originCube_iff.mp hx0) i
  simp only [zpow_zero, x] at hxi
  obtain ⟨h1, h2⟩ := hxi
  rw [lt_div_iff₀ hr] at h1
  rw [div_lt_iff₀ hr] at h2
  constructor <;> linarith

/-- The grid-cell chart composed with the cube normalization of `R` is the root chart. -/
theorem aux_lem_as_coarse_ms_normalize_chart {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (n : ℕ) {R : Homogenization.TriadicCube d} (hscale : R.scale = -(n : ℤ))
    (x : Homogenization.Vec d) :
    (fun i => aux_lem_as_coarse_ms_cellCenter z r n R.index i +
        r * (3 : ℝ) ^ (-(n : ℤ)) * aux_lem_extension_cell_moment_cubeNormalize R x i) =
      fun i => z i + r * x i := by
  have hmul : (3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ (-R.scale) = 1 := by
    rw [hscale, neg_neg, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
  funext i
  simp only [aux_lem_as_coarse_ms_cellCenter, aux_lem_extension_cell_moment_cubeNormalize,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination r * x i * hmul

/-- **Chart transport.**  The cell matrices of a depth-`n` descendant `R` in the root chart are
the cell matrices of the unit root in the chart of the grid cell `z + r 3^{-n}(v + Q₀)`. -/
theorem aux_lem_as_coarse_ms_chart_transport {d : ℕ} (Jc : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (n : ℕ)
    {R : Homogenization.TriadicCube d}
    (hR : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (n : ℤ))) :
    coarseBMatrixNorm R (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) =
        coarseBMatrixNorm (Homogenization.originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (aux_lem_as_coarse_ms_cellCenter z r n R.index) (r * (3 : ℝ) ^ (-(n : ℤ)))) ∧
      coarseSigmaStarInvMatrixNorm R
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) =
        coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (aux_lem_as_coarse_ms_cellCenter z r n R.index) (r * (3 : ℝ) ^ (-(n : ℤ)))) := by
  set w := aux_lem_as_coarse_ms_cellCenter z r n R.index with hw
  set r' : ℝ := r * (3 : ℝ) ^ (-(n : ℤ)) with hr'def
  have hr' : 0 < r' := by positivity
  have hscale := aux_lem_as_coarse_ms_desc_scale hR
  have hsub := aux_lem_as_coarse_ms_cell_sub z r hr n hR hr'
  let F : SpatialCoordinates d → ℝ := cutoffCoefficient M H om N
  have hFc : Continuous F := cutoffCoefficient_continuous M H om N
  have hFpos : ∀ y, 0 < F y := fun y =>
    mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)
  let f : C(Homogenization.Vec d, ℝ) :=
    ⟨fun y => F (fun i => w i + r' * y i), hFc.comp (by fun_prop)⟩
  have hf : ∀ y, 0 < f y := fun y => hFpos _
  let a0 := (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) w r').coeffOn
    (Homogenization.originCube d 0)
  have ha0 : ∀ᵐ x ∂Homogenization.volumeMeasureOn
      (Homogenization.openCubeSet (Homogenization.originCube d 0)),
      a0.toCoeffField x = Homogenization.scalarMatrix (f x) :=
    aux_lem_extension_cell_moment_chart_scalar_identity Jc M H om N z r hr w r' hr' hsub
      (Homogenization.originCube d 0) subset_rfl
  obtain ⟨aQ, haQ, _, hJ⟩ := aux_lem_extension_cell_moment_reference_on_cube R f hf a0 ha0
  have hroot := aux_lem_extension_cell_moment_chart_scalar_identity Jc M H om N z r hr z r hr
    subset_rfl R (aux_lem_as_coarse_ms_desc_sub hR)
  have hAE : CoeffOn.AEEq
      ((Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r).coeffOn R) aQ := by
    unfold CoeffOn.AEEq
    filter_upwards [hroot] with x hx
    rw [hx, haQ x]
    congr 1
    change F (fun i => z i + r * x i) =
      F (fun i => w i + r' * aux_lem_extension_cell_moment_cubeNormalize R x i)
    congr 1
    exact (aux_lem_as_coarse_ms_normalize_chart z r n hscale x).symm
  have hJall : ∀ p q, responseJ (cubeDomain R)
      ((Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r).coeffOn R) p q =
      responseJ (cubeDomain (Homogenization.originCube d 0)) a0 p q := fun p q =>
    (responseJ_eq_ofAEEq hAE p q).trans (hJ p q)
  obtain ⟨hb, hs⟩ := aux_lem_as_coarse_ms_coarse_congr hJall
  exact ⟨by unfold coarseBMatrixNorm; rw [hb], by unfold coarseSigmaStarInvMatrixNorm; rw [hs]⟩

end Paper

end SegTransport

section SegOnNode

open scoped BigOperators ENNReal NNReal
open MeasureTheory Filter
open Homogenization.Book.Ch02
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

namespace Paper

/-- `3^{c N} → ∞` along the naturals for `c > 0`. -/
theorem aux_lem_as_coarse_ms_eventually_rpow_ge {c : ℝ} (hc : 0 < c) (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ (3 : ℝ) ^ (c * (N : ℝ)) := by
  have h1 : 1 < (3 : ℝ) ^ c := Real.one_lt_rpow (by norm_num) hc
  have ht := tendsto_pow_atTop_atTop_of_one_lt h1
  filter_upwards [ht.eventually_ge_atTop A] with N hN
  rwa [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]

/-- **Arbitrary triadic roots.**  The landed assembly (`lem_as_coarse_multiscale_assembly`)
applied to the reindexed cutoff `N' ↦ N' + m`: deep bounds are needed only up to root depth
`N - m`, and the remaining cells use the sub-wavelength bound.  This is the case of a root of
side `3^{-m}`, whose physical wavelength sits at root depth `N - m`.  Uses the paper's strict
`ξ < (s-ρ)θ`. -/
theorem aux_lem_as_coarse_ms_uniform_offset {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (coef : ℕ → PositiveCoefficient (centeredCube z r hr))
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (rho theta xi : ℝ) (hrhos : rho < s)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1) (hxi0 : 0 ≤ xi) (hxi : xi < (s - rho) * theta)
    (m N0 : ℕ) (K Ksub : ℝ) (Kdeep S : ℕ → ℝ)
    (hK : 0 ≤ K) (hKd : ∀ N, 0 ≤ Kdeep N) (hS : ∀ N, 0 ≤ S N)
    (hKdN : ∀ N, N0 ≤ N → Kdeep N ≤ (3 : ℝ) ^ (xi * (N : ℝ)))
    (hSN : ∀ N, N0 ≤ N → (3 : ℝ) ^ (-(s * (N : ℝ))) * S N ≤ Ksub)
    (hshallow : ∀ N, N0 ≤ N → ∀ n : ℕ, (n : ℝ) ≤ theta * N →
      ∀ R ∈ aux_lem_as_coarse_ms_desc d n,
        coarseBMatrixNorm R (Jc.chart z r hr (coef N) z r) ≤ K * (3 : ℝ) ^ (rho * (n : ℝ)) ∧
          coarseSigmaStarInvMatrixNorm R (Jc.chart z r hr (coef N) z r) ≤
            K * (3 : ℝ) ^ (rho * (n : ℝ)))
    (hdeep : ∀ N, N0 ≤ N → ∀ n : ℕ, theta * N < (n : ℝ) → n + m ≤ N →
      ∀ R ∈ aux_lem_as_coarse_ms_desc d n,
        coarseBMatrixNorm R (Jc.chart z r hr (coef N) z r) ≤
            Kdeep N * (3 : ℝ) ^ (rho * (n : ℝ)) ∧
          coarseSigmaStarInvMatrixNorm R (Jc.chart z r hr (coef N) z r) ≤
            Kdeep N * (3 : ℝ) ^ (rho * (n : ℝ)))
    (hsub : ∀ N, N0 ≤ N → ∀ n : ℕ, N < n + m → ∀ R ∈ aux_lem_as_coarse_ms_desc d n,
      coarseBMatrixNorm R (Jc.chart z r hr (coef N) z r) ≤ S N ∧
        coarseSigmaStarInvMatrixNorm R (Jc.chart z r hr (coef N) z r) ≤ S N) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ qe : ℝ≥0∞, (qe = 1 ∨ qe = 2) →
      Jc.Lam z r hr (coef N) z r s qe + (Jc.lam z r hr (coef N) z r s qe)⁻¹ ≤ C := by
  set xi' : ℝ := (xi + (s - rho) * theta) / 2 with hxi'def
  have hxi'1 : xi < xi' := by rw [hxi'def]; linarith
  have hxi'2 : xi' ≤ (s - rho) * theta := by rw [hxi'def]; linarith
  have hgap : 0 < xi' - xi := by linarith
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp
    (aux_lem_as_coarse_ms_eventually_rpow_ge hgap (K + (3 : ℝ) ^ (xi * (m : ℝ))))
  set N0' : ℕ := max N0 N1 with hN0'
  -- the reindexed data
  have hKdN' : ∀ N', N0' ≤ N' → K + Kdeep (N' + m) ≤ (3 : ℝ) ^ (xi' * (N' : ℝ)) := by
    intro N' hN'
    have hA := hN1 N' (le_trans (le_max_right _ _) hN')
    have hB := hKdN (N' + m) (le_trans (le_max_left _ _) (le_trans hN' (Nat.le_add_right _ _)))
    have hsplit : (3 : ℝ) ^ (xi * ((N' + m : ℕ) : ℝ)) =
        (3 : ℝ) ^ (xi * (m : ℝ)) * (3 : ℝ) ^ (xi * (N' : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]; push_cast; ring_nf
    have hsplit' : (3 : ℝ) ^ (xi' * (N' : ℝ)) =
        (3 : ℝ) ^ ((xi' - xi) * (N' : ℝ)) * (3 : ℝ) ^ (xi * (N' : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]; ring_nf
    have hone : 1 ≤ (3 : ℝ) ^ (xi * (N' : ℝ)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg hxi0 (Nat.cast_nonneg _))
    rw [hsplit] at hB
    rw [hsplit']
    have hpos : 0 ≤ (3 : ℝ) ^ (xi * (m : ℝ)) := by positivity
    nlinarith
  have hSN' : ∀ N', N0' ≤ N' →
      (3 : ℝ) ^ (-(s * (N' : ℝ))) * S (N' + m) ≤ (3 : ℝ) ^ (s * (m : ℝ)) * Ksub := by
    intro N' hN'
    have h := hSN (N' + m) (le_trans (le_max_left _ _) (le_trans hN' (Nat.le_add_right _ _)))
    have hsplit : (3 : ℝ) ^ (-(s * (N' : ℝ))) =
        (3 : ℝ) ^ (s * (m : ℝ)) * (3 : ℝ) ^ (-(s * ((N' + m : ℕ) : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]; push_cast; ring_nf
    rw [hsplit, mul_assoc]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  obtain ⟨C', hC', hbound⟩ := lem_as_coarse_multiscale_assembly hd Jc z r hr
    (fun N' => coef (N' + m)) s hs rho theta xi' hrhos htheta.le htheta1 hxi'2 N0' K
    ((3 : ℝ) ^ (s * (m : ℝ)) * Ksub) (fun N' => K + Kdeep (N' + m)) (fun N' => S (N' + m))
    hK (fun N' => add_nonneg hK (hKd _)) (fun N' => hS _) hKdN' hSN'
    (by
      intro N' hN' n hn R hR
      have hN : N0 ≤ N' + m := le_trans (le_max_left _ _) (le_trans hN' (Nat.le_add_right _ _))
      refine hshallow (N' + m) hN n ?_ R hR
      have : theta * (N' : ℝ) ≤ theta * ((N' + m : ℕ) : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ htheta.le; exact_mod_cast Nat.le_add_right _ _
      linarith)
    (by
      intro N' hN' n hn hnN R hR
      have hN : N0 ≤ N' + m := le_trans (le_max_left _ _) (le_trans hN' (Nat.le_add_right _ _))
      have h3 : 0 ≤ (3 : ℝ) ^ (rho * (n : ℝ)) := by positivity
      by_cases hsh : (n : ℝ) ≤ theta * ((N' + m : ℕ) : ℝ)
      · obtain ⟨h1, h2⟩ := hshallow (N' + m) hN n hsh R hR
        have hKd' := hKd (N' + m)
        constructor <;> nlinarith
      · obtain ⟨h1, h2⟩ := hdeep (N' + m) hN n (not_le.1 hsh) (by omega) R hR
        constructor <;> nlinarith)
    (by
      intro N' hN' n hn R hR
      have hN : N0 ≤ N' + m := le_trans (le_max_left _ _) (le_trans hN' (Nat.le_add_right _ _))
      exact hsub (N' + m) hN n (by omega) R hR)
  let v : ℕ → ℝ≥0∞ → ℝ := fun N qe =>
    Jc.Lam z r hr (coef N) z r s qe + (Jc.lam z r hr (coef N) z r s qe)⁻¹
  let C0 : ℝ := ∑ N ∈ Finset.range m, (|v N 1| + |v N 2|)
  have hC0 : 0 ≤ C0 := Finset.sum_nonneg fun N _ => by positivity
  refine ⟨C' + C0 + 1, by linarith, ?_⟩
  intro N qe hqe
  change v N qe ≤ _
  rcases lt_or_ge N m with hN | hN
  · have hmem : N ∈ Finset.range m := Finset.mem_range.2 hN
    have hle : |v N 1| + |v N 2| ≤ C0 :=
      Finset.single_le_sum (f := fun N => |v N 1| + |v N 2|)
        (fun N _ => by positivity) hmem
    have hvq : v N qe ≤ |v N 1| + |v N 2| := by
      rcases hqe with rfl | rfl
      · linarith [le_abs_self (v N 1), abs_nonneg (v N 2)]
      · linarith [le_abs_self (v N 2), abs_nonneg (v N 1)]
    linarith
  · obtain ⟨N', rfl⟩ : ∃ N', N = N' + m := ⟨N - m, by omega⟩
    have h := hbound N' qe hqe
    change v (N' + m) qe ≤ C' at h
    linarith

/-- **Pathwise multiscale assembly from grid-cell matrices** (any triadic root; `m` is the
root's depth below the unit scale, `0` for roots of side `≥ 1`). -/
theorem aux_lem_as_coarse_ms_pathwise_cells {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (rho theta xi : ℝ) (hrhos : rho < s)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1) (hxi0 : 0 ≤ xi) (hxi : xi < (s - rho) * theta)
    (m N0 : ℕ) (K Ksub : ℝ) (Kdeep lo hi : ℕ → ℝ)
    (hK : 0 ≤ K) (hKd : ∀ N, 0 ≤ Kdeep N) (hlo : ∀ N, 0 < lo N) (hle : ∀ N, lo N ≤ hi N)
    (hKdN : ∀ N, N0 ≤ N → Kdeep N ≤ (3 : ℝ) ^ (xi * (N : ℝ)))
    (hSN : ∀ N, N0 ≤ N → (3 : ℝ) ^ (-(s * (N : ℝ))) * (hi N + (lo N)⁻¹) ≤ Ksub)
    (hshallow : ∀ N, N0 ≤ N → ∀ k : ℕ, (k : ℝ) ≤ theta * N → ∀ nidx : Fin d → ℤ,
      (centeredCube (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
          (r * (3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      coarseBMatrixNorm (Homogenization.originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤ K * (3 : ℝ) ^ (rho * (k : ℝ)) ∧
        coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤ K * (3 : ℝ) ^ (rho * (k : ℝ)))
    (hdeep : ∀ N, N0 ≤ N → ∀ k : ℕ, theta * N < (k : ℝ) → k + m ≤ N → ∀ nidx : Fin d → ℤ,
      (centeredCube (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
          (r * (3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      coarseBMatrixNorm (Homogenization.originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤ Kdeep N * (3 : ℝ) ^ (rho * (k : ℝ)) ∧
        coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤ Kdeep N * (3 : ℝ) ^ (rho * (k : ℝ)))
    (hext : ∀ N, N0 ≤ N → ∀ y ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      lo N ≤ cutoffCoefficient M H om N y ∧ cutoffCoefficient M H om N y ≤ hi N) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ qe : ℝ≥0∞, (qe = 1 ∨ qe = 2) →
      Jc.Lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s qe +
        (Jc.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s qe)⁻¹ ≤ C := by
  refine aux_lem_as_coarse_ms_uniform_offset hd Jc z r hr
    (fun N => cutoffPositiveCoefficient M H om N z hr) s hs rho theta xi hrhos htheta htheta1
    hxi0 hxi m N0 K Ksub Kdeep (fun N => hi N + (lo N)⁻¹) hK hKd
    (fun N => add_nonneg (le_trans (hlo N).le (hle N)) (inv_nonneg.2 (hlo N).le))
    hKdN hSN ?_ ?_ ?_
  · intro N hN n hn R hR
    obtain ⟨hb, hsg⟩ := aux_lem_as_coarse_ms_chart_transport Jc M H om N z r hr n hR
    have hr' : 0 < r * (3 : ℝ) ^ (-(n : ℤ)) := by positivity
    have hcell := hshallow N hN n hn R.index (aux_lem_as_coarse_ms_cell_sub z r hr n hR hr')
    rw [hb, hsg]
    exact hcell
  · intro N hN n hn hnN R hR
    obtain ⟨hb, hsg⟩ := aux_lem_as_coarse_ms_chart_transport Jc M H om N z r hr n hR
    have hr' : 0 < r * (3 : ℝ) ^ (-(n : ℤ)) := by positivity
    have hcell := hdeep N hN n hn hnN R.index (aux_lem_as_coarse_ms_cell_sub z r hr n hR hr')
    rw [hb, hsg]
    exact hcell
  · intro N hN n _ R hR
    have hae := aux_lem_as_coarse_ms_cutoff_ae_bounds M H om N z r hr (hext N hN)
    obtain ⟨hb, hsg⟩ := aux_lem_as_coarse_ms_chart_norms_le hd Jc z r hr
      (cutoffPositiveCoefficient M H om N z hr) z r hr subset_rfl (hlo N) (hle N) hae R
      (aux_lem_as_coarse_ms_desc_sub hR)
    have h1 : 0 ≤ (lo N)⁻¹ := inv_nonneg.2 (hlo N).le
    have h2 : 0 ≤ hi N := le_trans (hlo N).le (hle N)
    exact ⟨by linarith, by linarith⟩

/-- A bound on the `in_J` pair `Λ + λ⁻¹` of a grid cell (the form of `lem_extension`'s grid
clause) bounds both cell matrices of that cell. -/
theorem aux_lem_as_coarse_ms_cell_of_Lam {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (qe : ℝ≥0∞) (hqe : 1 ≤ qe) (hqt : qe ≠ ⊤) {X : ℝ}
    (hX : Jc.Lam z r hr a w r' s qe + (Jc.lam z r hr a w r' s qe)⁻¹ ≤ X) :
    coarseBMatrixNorm (Homogenization.originCube d 0) (Jc.chart z r hr a w r') ≤ X ∧
      coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0) (Jc.chart z r hr a w r') ≤
        X := by
  haveI : NeZero d := ⟨by omega⟩
  have hq1 : 1 ≤ qe.toReal := by
    have := ENNReal.toReal_mono hqt hqe
    simpa using this
  have hL := Jc.Lam_eq z r hr a w r' hr' hsub s hs qe hqe
  have hl := Jc.lam_eq z r hr a w r' hr' hsub s hs qe hqe
  rw [if_neg hqt] at hL hl
  have hb := oneCube_b_le_LambdaSq_finite (Homogenization.originCube d 0)
    (Jc.chart z r hr a w r') hs.1 hq1
  have hsg := oneCube_sigmaStarInv_le_lambdaSq_finite_inv (Homogenization.originCube d 0)
    (Jc.chart z r hr a w r') hs.1 hq1
  rw [← hL] at hb
  rw [← hl] at hsg
  have hLp := (Jc.Lam_pos z r hr a w r' s qe).le
  have hlp := (inv_pos.2 (Jc.lam_pos z r hr a w r' s qe)).le
  exact ⟨by linarith, by linarith⟩

/-- The paper-faithful per-sample inputs of the first clause for one infrared convention `H`:
retained and deep grid-cell matrices (in the cells' own charts) and a pointwise envelope of
`A_N` on the root, all for `N ≥ N₀`. -/
def aux_lem_as_coarse_ms_Inputs {d : ℕ} (Jc : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s rho theta xi : ℝ) (m : ℕ) : Prop :=
  ∃ (N0 : ℕ) (K Ksub : ℝ) (Kdeep lo hi : ℕ → ℝ),
    0 ≤ K ∧ (∀ N, 0 ≤ Kdeep N) ∧ (∀ N, 0 < lo N) ∧ (∀ N, lo N ≤ hi N) ∧
    (∀ N, N0 ≤ N → Kdeep N ≤ (3 : ℝ) ^ (xi * (N : ℝ))) ∧
    (∀ N, N0 ≤ N → (3 : ℝ) ^ (-(s * (N : ℝ))) * (hi N + (lo N)⁻¹) ≤ Ksub) ∧
    (∀ N, N0 ≤ N → ∀ k : ℕ, (k : ℝ) ≤ theta * N → ∀ nidx : Fin d → ℤ,
      (centeredCube (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
          (r * (3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      coarseBMatrixNorm (Homogenization.originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤ K * (3 : ℝ) ^ (rho * (k : ℝ)) ∧
        coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤ K * (3 : ℝ) ^ (rho * (k : ℝ))) ∧
    (∀ N, N0 ≤ N → ∀ k : ℕ, theta * N < (k : ℝ) → k + m ≤ N → ∀ nidx : Fin d → ℤ,
      (centeredCube (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
          (r * (3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      coarseBMatrixNorm (Homogenization.originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤ Kdeep N * (3 : ℝ) ^ (rho * (k : ℝ)) ∧
        coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤ Kdeep N * (3 : ℝ) ^ (rho * (k : ℝ))) ∧
    (∀ N, N0 ≤ N → ∀ y ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      lo N ≤ cutoffCoefficient M H om N y ∧ cutoffCoefficient M H om N y ≤ hi N)

theorem aux_lem_as_coarse_ms_of_inputs {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (rho theta xi : ℝ) (hrhos : rho < s)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1) (hxi0 : 0 ≤ xi) (hxi : xi < (s - rho) * theta)
    (m : ℕ)
    (hin : aux_lem_as_coarse_ms_Inputs Jc M H om z r hr s rho theta xi m) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ qe : ℝ≥0∞, (qe = 1 ∨ qe = 2) →
      Jc.Lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s qe +
        (Jc.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s qe)⁻¹ ≤ C := by
  obtain ⟨N0, K, Ksub, Kdeep, lo, hi, hK, hKd, hlo, hle, hKdN, hSN, hsh, hdp, hext⟩ := hin
  exact aux_lem_as_coarse_ms_pathwise_cells hd Jc M H om z r hr s hs rho theta xi hrhos htheta
    htheta1 hxi0 hxi m N0 K Ksub Kdeep lo hi hK hKd hlo hle hKdN hSN hsh hdp hext

/-- **Consumer form: the parent's first clause at one sample**, verbatim in both infrared
conventions (`lem_as_coarse`, `let Hc := if withIR then Hir else 0`). -/
theorem lem_as_coarse_first_clause_assembly {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (rho theta xi : ℝ) (hrhos : rho < s)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1) (hxi0 : 0 ≤ xi) (hxi : xi < (s - rho) * theta)
    (m : ℕ)
    (hin : ∀ withIR : Bool, aux_lem_as_coarse_ms_Inputs Jc M
      (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) om z r hr
      s rho theta xi m) :
    ∃ K : ℝ, 0 < K ∧ ∀ withIR : Bool,
      let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
        if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ));
      ∀ (qe : ℝ≥0∞), (qe = 1 ∨ qe = 2) → ∀ N : ℕ,
        Jc.Lam z r hr (cutoffPositiveCoefficient M Hc om N z hr) z r s qe +
            (Jc.lam z r hr (cutoffPositiveCoefficient M Hc om N z hr) z r s qe)⁻¹ ≤ K := by
  obtain ⟨Ct, hCt, ht⟩ := aux_lem_as_coarse_ms_of_inputs hd Jc M _ om z r hr s hs rho theta xi
    hrhos htheta htheta1 hxi0 hxi m (hin true)
  obtain ⟨Cf, hCf, hf⟩ := aux_lem_as_coarse_ms_of_inputs hd Jc M _ om z r hr s hs rho theta xi
    hrhos htheta htheta1 hxi0 hxi m (hin false)
  refine ⟨max Ct Cf, lt_max_of_lt_left hCt, ?_⟩
  intro withIR
  cases withIR with
  | true => exact fun qe hqe N => (ht N qe hqe).trans (le_max_left _ _)
  | false => exact fun qe hqe N => (hf N qe hqe).trans (le_max_right _ _)



theorem aux_lem_as_coarse_ms_grid_cell_matrix {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (a : PositiveCoefficient (centeredCube z0 R hR))
    (w : SpatialCoordinates d) (k : ℕ)
    (hsub : (centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) :
      Set (SpatialCoordinates d)) ⊆ (centeredCube z0 R hR : Set (SpatialCoordinates d)))
    (s0 : ℝ) (hs0 : s0 ∈ Set.Ioc (0 : ℝ) 1) (eta K : ℝ)
    (hX : Jc.Lam z0 R hR a w ((3 : ℝ) ^ (-(k : ℤ))) s0 2 +
        (Jc.lam z0 R hR a w ((3 : ℝ) ^ (-(k : ℤ))) s0 2)⁻¹ ≤
      K * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-eta)) :
    coarseBMatrixNorm (Homogenization.originCube d 0)
        (Jc.chart z0 R hR a w ((3 : ℝ) ^ (-(k : ℤ)))) ≤ K * (3 : ℝ) ^ (eta * (k : ℝ)) ∧
      coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
        (Jc.chart z0 R hR a w ((3 : ℝ) ^ (-(k : ℤ)))) ≤ K * (3 : ℝ) ^ (eta * (k : ℝ)) := by
  have hpow : ((3 : ℝ) ^ (-(k : ℤ))) ^ (-eta) = (3 : ℝ) ^ (eta * (k : ℝ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  rw [hpow] at hX
  exact aux_lem_as_coarse_ms_cell_of_Lam hd Jc z0 R hR a w _ (by positivity) hsub s0 hs0 2
    (by norm_num) (by norm_num) hX

end Paper

end SegOnNode
