module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic
public import Homogenization.Ambient.MatrixOrderBridge
public import Homogenization.Ambient.ScalarMatrix
public import Homogenization.Deterministic.MultiscaleQuantitiesBasic.Foundation.Geometry
public import Homogenization.Geometry.CubeMeasure

@[expose] public section




open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

open Homogenization.Book.Ch02
open Homogenization (Vec Mat vecDot vecNormSq matVecMul MatLoewnerLE)

/-! ## A. Scalar multiples of the identity -/

theorem aux_lem_as_coarse_scalar_cell_bridge_quad_smul_one {d : ℕ} (c : ℝ) (x : Vec d) :
    vecDot x (matVecMul (c • (1 : Mat d)) x) = c * vecNormSq x := by
  have h := Homogenization.matVecMul_scalarMatrix (d := d) c x
  change vecDot x (matVecMul (Homogenization.scalarMatrix (d := d) c) x) = _
  rw [h, Homogenization.vecDot_smul_right]
  rfl

theorem aux_lem_as_coarse_scalar_cell_bridge_loewner_smul_one {d : ℕ} {c c' : ℝ} (h : c ≤ c') :
    MatLoewnerLE (c • (1 : Mat d)) (c' • (1 : Mat d)) := by
  intro x
  rw [aux_lem_as_coarse_scalar_cell_bridge_quad_smul_one, aux_lem_as_coarse_scalar_cell_bridge_quad_smul_one]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right h (Homogenization.vecNormSq_nonneg x)) (by norm_num)

theorem aux_lem_as_coarse_scalar_cell_bridge_matrixNorm_smul_one {d : ℕ} [NeZero d] {c : ℝ} (hc : 0 ≤ c) :
    matrixNorm (c • (1 : Mat d)) = c := by
  rw [matrixNorm_eq_matrixOperatorNorm, matrixOperatorNorm_smul_one_eq_of_nonneg hc]

theorem aux_lem_as_coarse_scalar_cell_bridge_inv_smul_one {d : ℕ} {c : ℝ} (hc : c ≠ 0) :
    (c • (1 : Mat d))⁻¹ = c⁻¹ • (1 : Mat d) := by
  apply Matrix.inv_eq_left_inv
  rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, one_mul, one_smul]

theorem aux_lem_as_coarse_scalar_cell_bridge_symmPart_smul_one {d : ℕ} (c : ℝ) :
    Homogenization.symmPart (c • (1 : Mat d)) = c • (1 : Mat d) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Homogenization.symmPart]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [Homogenization.symmPart, hij, hji]

/-! ## B. Averages of a.e. scalar fields -/

theorem aux_lem_as_coarse_scalar_cell_bridge_volume_pos {d : ℕ} (U : Domain d) :
    0 < (volume (U : Set (Vec d))).toReal := by
  have hpos : 0 < volume (U : Set (Vec d)) := U.isOpen.measure_pos volume U.nonempty
  have hfin : volume (U : Set (Vec d)) < ⊤ := by
    have h := measure_lt_top (volume.restrict (U : Set (Vec d))) Set.univ
    rwa [Measure.restrict_apply_univ] at h
  exact ENNReal.toReal_pos hpos.ne' hfin.ne

theorem aux_lem_as_coarse_scalar_cell_bridge_averageMat_smul_one {d : ℕ} (U : Domain d) (G : Vec d → Mat d)
    (g : Vec d → ℝ)
    (hG : ∀ᵐ x ∂volume.restrict (U : Set (Vec d)), G x = g x • (1 : Mat d)) :
    averageMat U G = Homogenization.Book.Ch02.average U g • (1 : Mat d) := by
  ext i j
  change Homogenization.Book.Ch02.average U (fun x => G x i j) = Homogenization.Book.Ch02.average U g * (1 : Mat d) i j
  have hint : ∫ x in (U : Set (Vec d)), G x i j =
      ∫ x in (U : Set (Vec d)), g x * (1 : Mat d) i j := by
    refine integral_congr_ae ?_
    filter_upwards [hG] with x hx
    rw [hx]
    rfl
  unfold Homogenization.Book.Ch02.average
  rw [hint, integral_mul_const]
  ring

theorem aux_lem_as_coarse_scalar_cell_bridge_average_le {d : ℕ} (U : Domain d) {g : Vec d → ℝ} {M : ℝ}
    (hg0 : ∀ᵐ x ∂volume.restrict (U : Set (Vec d)), 0 ≤ g x)
    (hgM : ∀ᵐ x ∂volume.restrict (U : Set (Vec d)), g x ≤ M) :
    Homogenization.Book.Ch02.average U g ≤ M := by
  have hvol := aux_lem_as_coarse_scalar_cell_bridge_volume_pos U
  have hint : ∫ x in (U : Set (Vec d)), g x ≤ ∫ _x in (U : Set (Vec d)), M :=
    integral_mono_of_nonneg hg0 (integrable_const M) hgM
  rw [setIntegral_const, smul_eq_mul] at hint
  unfold Homogenization.Book.Ch02.average
  rw [inv_mul_le_iff₀ hvol]
  exact hint

theorem aux_lem_as_coarse_scalar_cell_bridge_le_average {d : ℕ} (U : Domain d) {g : Vec d → ℝ} {m : ℝ}
    (hg : Integrable g (volume.restrict (U : Set (Vec d))))
    (hmg : ∀ᵐ x ∂volume.restrict (U : Set (Vec d)), m ≤ g x) :
    m ≤ Homogenization.Book.Ch02.average U g := by
  have hvol := aux_lem_as_coarse_scalar_cell_bridge_volume_pos U
  have hint : ∫ _x in (U : Set (Vec d)), m ≤ ∫ x in (U : Set (Vec d)), g x :=
    integral_mono_ae (integrable_const m) hg hmg
  rw [setIntegral_const, smul_eq_mul] at hint
  unfold Homogenization.Book.Ch02.average
  rw [le_inv_mul_iff₀ hvol]
  exact hint

/-! ## C. The deterministic cell bound for an a.e. scalar coefficient -/

/-- **Scalar cell bound.**  If a Ch02 coefficient is a.e. the scalar matrix `f(x) I` with
`mlow ≤ f ≤ mhigh`, `0 < mlow`, then `|b(U)| ≤ mhigh` and `|σ_*⁻¹(U)| ≤ mlow⁻¹`. -/
theorem aux_lem_as_coarse_scalar_cell_bridge_coeffOn_bounds {d : ℕ} [NeZero d] (U : Domain d) (A : CoeffOn U)
    (f : Vec d → ℝ) {mlow mhigh : ℝ} (hmlow : 0 < mlow)
    (hA : ∀ᵐ x ∂volume.restrict (U : Set (Vec d)),
      A.toCoeffField x = Homogenization.scalarMatrix (f x) ∧ mlow ≤ f x ∧ f x ≤ mhigh) :
    matrixNorm (bCoarse U A) ≤ mhigh ∧ matrixNorm (sigmaStarInvCoarse U A) ≤ mlow⁻¹ := by
  have hA' : ∀ᵐ x ∂volume.restrict (U : Set (Vec d)),
      A.toCoeffField x = f x • (1 : Mat d) ∧ mlow ≤ f x ∧ f x ≤ mhigh := hA
  have hvol := aux_lem_as_coarse_scalar_cell_bridge_volume_pos U
  have hμ : volume.restrict (U : Set (Vec d)) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    intro h0
    rw [h0, ENNReal.toReal_zero] at hvol
    exact lt_irrefl _ hvol
  have : (ae (volume.restrict (U : Set (Vec d)))).NeBot := ae_neBot.2 hμ
  have hle : mlow ≤ mhigh := by
    obtain ⟨x, hx⟩ := hA'.exists
    exact hx.2.1.trans hx.2.2
  have hmhigh : 0 < mhigh := hmlow.trans_le hle
  -- the symmetric Dirichlet--Neumann package
  have hsym : CoeffOn.IsSymmetric A := by
    unfold CoeffOn.IsSymmetric
    filter_upwards [hA] with x hx
    rw [hx.1]
    exact Homogenization.scalarMatrix_isSymm _
  have T := responseSymmetricDirichletNeumannTheory U A hsym
  have hbσ : bCoarse U A = sigmaCoarse U A := T.derived_matrices.2.2
  obtain ⟨hH, -, hσavg⟩ := T.dirichlet_neumann_bracketing
  -- upper bound: `b = σ ≤ ⨍ a ≤ mhigh`
  have havg : averageMat U A.toCoeffField = Homogenization.Book.Ch02.average U f • (1 : Mat d) :=
    aux_lem_as_coarse_scalar_cell_bridge_averageMat_smul_one U _ f (hA'.mono fun x hx => hx.1)
  have hfavg : Homogenization.Book.Ch02.average U f ≤ mhigh :=
    aux_lem_as_coarse_scalar_cell_bridge_average_le U (hA'.mono fun x hx => (hmlow.trans_le hx.2.1).le)
      (hA'.mono fun x hx => hx.2.2)
  have hσle : MatLoewnerLE (sigmaCoarse U A) (mhigh • (1 : Mat d)) := by
    rw [havg] at hσavg
    exact hσavg.trans (aux_lem_as_coarse_scalar_cell_bridge_loewner_smul_one hfavg)
  have hσpsd : (sigmaCoarse U A).PosSemidef := hbσ ▸ bCoarse_posSemidef U A
  have hup : matrixNorm (bCoarse U A) ≤ mhigh := by
    rw [hbσ]
    calc matrixNorm (sigmaCoarse U A) ≤ matrixNorm (mhigh • (1 : Mat d)) :=
          matrixNorm_le_of_matLoewnerLE_of_posSemidef hσpsd
            (Matrix.PosSemidef.one.smul hmhigh.le) hσle
      _ = mhigh := aux_lem_as_coarse_scalar_cell_bridge_matrixNorm_smul_one hmhigh.le
  -- lower bound: `mlow ≤ (⨍ a⁻¹)⁻¹ ≤ σ_*`, then invert
  have hfmeas : AEStronglyMeasurable f (volume.restrict (U : Set (Vec d))) := by
    refine (A.aeStronglyMeasurable 0 0).congr ?_
    filter_upwards [hA', ae_restrict_mem U.measurableSet] with x hx hxU
    rw [Homogenization.restrictCoeffField_apply_of_mem hxU, hx.1]
    simp
  have hinvint : Integrable (fun x => (f x)⁻¹) (volume.restrict (U : Set (Vec d))) := by
    refine Integrable.of_bound hfmeas.aemeasurable.inv.aestronglyMeasurable mlow⁻¹ ?_
    filter_upwards [hA'] with x hx
    have hfx : 0 < f x := hmlow.trans_le hx.2.1
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hfx)]
    exact inv_anti₀ hmlow hx.2.1
  have hinvavg : averagedSymmPartInv U A =
      Homogenization.Book.Ch02.average U (fun x => (f x)⁻¹) • (1 : Mat d) := by
    unfold averagedSymmPartInv
    refine aux_lem_as_coarse_scalar_cell_bridge_averageMat_smul_one U _ _ ?_
    filter_upwards [hA'] with x hx
    rw [hx.1, aux_lem_as_coarse_scalar_cell_bridge_symmPart_smul_one,
      aux_lem_as_coarse_scalar_cell_bridge_inv_smul_one (hmlow.trans_le hx.2.1).ne']
  have hh_pos : 0 < Homogenization.Book.Ch02.average U (fun x => (f x)⁻¹) :=
    lt_of_lt_of_le (inv_pos.2 hmhigh)
      (aux_lem_as_coarse_scalar_cell_bridge_le_average U hinvint
        (hA'.mono fun x hx => inv_anti₀ (hmlow.trans_le hx.2.1) hx.2.2))
  have hh_le : Homogenization.Book.Ch02.average U (fun x => (f x)⁻¹) ≤ mlow⁻¹ :=
    aux_lem_as_coarse_scalar_cell_bridge_average_le U
      (hA'.mono fun x hx => (inv_pos.2 (hmlow.trans_le hx.2.1)).le)
      (hA'.mono fun x hx => inv_anti₀ hmlow hx.2.1)
  have hlowσ : MatLoewnerLE (mlow • (1 : Mat d)) (sigmaStarCoarse U A) := by
    rw [hinvavg, aux_lem_as_coarse_scalar_cell_bridge_inv_smul_one hh_pos.ne'] at hH
    refine (aux_lem_as_coarse_scalar_cell_bridge_loewner_smul_one ?_).trans hH
    rw [le_inv_comm₀ hmlow hh_pos]
    exact hh_le
  have hinv := Homogenization.matLoewnerLE_inv_of_posDef
    (Matrix.PosDef.one.smul hmlow) (sigmaStarCoarse_posDef U A) hlowσ
  have hSS : (sigmaStarCoarse U A)⁻¹ = sigmaStarInvCoarse U A := by
    unfold sigmaStarCoarse
    exact Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_sigmaStarInvCoarse U A)
  rw [hSS, aux_lem_as_coarse_scalar_cell_bridge_inv_smul_one hmlow.ne'] at hinv
  have hlo : matrixNorm (sigmaStarInvCoarse U A) ≤ mlow⁻¹ := by
    calc matrixNorm (sigmaStarInvCoarse U A) ≤ matrixNorm (mlow⁻¹ • (1 : Mat d)) :=
          matrixNorm_le_of_matLoewnerLE_of_posSemidef
            (sigmaStarInvCoarse_posDef U A).posSemidef
            (Matrix.PosSemidef.one.smul (inv_nonneg.2 hmlow.le)) hinv
      _ = mlow⁻¹ := aux_lem_as_coarse_scalar_cell_bridge_matrixNorm_smul_one (inv_nonneg.2 hmlow.le)
  exact ⟨hup, hlo⟩

/-! ## D. Affine chart geometry -/

/-- The unit root `openCubeSet (originCube d 0)` is the open cube `(-1/2, 1/2)^d`. -/
theorem aux_lem_as_coarse_scalar_cell_bridge_mem_unit_root {d : ℕ} {x : SpatialCoordinates d}
    (hx : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0)) (i : Fin d) :
    -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2 := by
  have h : ∀ i, -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2 := by
    simpa [Homogenization.openCubeSet, Homogenization.originCube,
      Homogenization.cubeScaleFactor] using hx
  exact h i

/-- The chart `x ↦ z + r x` maps the unit root into the open cube `centeredCube z r`. -/
theorem aux_lem_as_coarse_scalar_cell_bridge_affine_mem {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) {x : SpatialCoordinates d}
    (hx : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    (fun i => z i + r * x i) ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  rw [centeredCube_eq_pi]
  intro i _
  obtain ⟨h1, h2⟩ := aux_lem_as_coarse_scalar_cell_bridge_mem_unit_root hx i
  have h1' : r * (-(1 / 2 : ℝ)) < r * x i := mul_lt_mul_of_pos_left h1 hr
  have h2' : r * x i < r * (1 / 2 : ℝ) := mul_lt_mul_of_pos_left h2 hr
  constructor <;> linarith

/-- The affine chart is quasi-measure-preserving for Lebesgue measure. -/
theorem aux_lem_as_coarse_scalar_cell_bridge_qmp_affine {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) :
    Measure.QuasiMeasurePreserving (fun x : SpatialCoordinates d => fun i => z i + r * x i)
      volume volume := by
  have h1 : Measure.QuasiMeasurePreserving (fun y : SpatialCoordinates d => r • y)
      volume volume :=
    Measure.quasiMeasurePreserving_smul volume hr.ne'
  have h2 : Measure.QuasiMeasurePreserving (fun y : SpatialCoordinates d => y + z)
      volume volume :=
    (measurePreserving_add_right volume z).quasiMeasurePreserving
  have heq : (fun x : SpatialCoordinates d => fun i => z i + r * x i) =
      (fun y : SpatialCoordinates d => y + z) ∘ (fun y : SpatialCoordinates d => r • y) := by
    funext x i
    simp [add_comm]
  rw [heq]
  exact h2.comp h1

/-- A.e. statements on a set pull back along a quasi-measure-preserving map sending a
second set into the first. -/
theorem aux_lem_as_coarse_scalar_cell_bridge_ae_restrict_comp {d : ℕ}
    {f : SpatialCoordinates d → SpatialCoordinates d}
    (hf : Measure.QuasiMeasurePreserving f volume volume) {S S' : Set (SpatialCoordinates d)}
    (hS : MeasurableSet S) (hS' : MeasurableSet S') (hmaps : ∀ y ∈ S', f y ∈ S)
    {P : SpatialCoordinates d → Prop} (h : ∀ᵐ x ∂volume.restrict S, P x) :
    ∀ᵐ y ∂volume.restrict S', P (f y) := by
  rw [ae_restrict_iff' hS] at h
  rw [ae_restrict_iff' hS']
  filter_upwards [hf.ae h] with y hy hyS'
  exact hy (hmaps y hyS')






theorem aux_lem_as_coarse_scalar_cell_bridge_chart {d : ℕ} [NeZero d] (Jc : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) {mlow mhigh : ℝ} (hmlow : 0 < mlow)
    (hbd : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      mlow ≤ a.val y ∧ a.val y ≤ mhigh)
    (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆
      Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    coarseBMatrixNorm R (Jc.chart z r hr a z r) ≤ mhigh ∧
      coarseSigmaStarInvMatrixNorm R (Jc.chart z r hr a z r) ≤ mlow⁻¹ := by
  have hc := Jc.chart_eq z r hr a z r hr subset_rfl R hR
  have hRmeas : MeasurableSet (Homogenization.openCubeSet R) :=
    Homogenization.measurableSet_openCubeSet R
  have hmaps : ∀ x ∈ Homogenization.openCubeSet R,
      (fun i => z i + r * x i) ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    fun x hx => aux_lem_as_coarse_scalar_cell_bridge_affine_mem z r hr (hR hx)
  have hv := aux_lem_as_coarse_scalar_cell_bridge_ae_restrict_comp (aux_lem_as_coarse_scalar_cell_bridge_qmp_affine z r hr)
    (centeredCube z r hr).isOpen.measurableSet hRmeas hmaps hbd
  exact aux_lem_as_coarse_scalar_cell_bridge_coeffOn_bounds (cubeDomain R) ((Jc.chart z r hr a z r).coeffOn R)
    (fun x => a.val (fun i => z i + r * x i)) hmlow
    (by filter_upwards [hc, hv] with x h1 h2; exact ⟨h1, h2⟩)



theorem aux_lem_as_coarse_scalar_cell_bridge_chart_desc {d : ℕ} [NeZero d] (Jc : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) {mlow mhigh : ℝ} (hmlow : 0 < mlow)
    (hbd : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      mlow ≤ a.val y ∧ a.val y ≤ mhigh)
    (n : ℕ) (R : Homogenization.TriadicCube d)
    (hR : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (n : ℤ))) :
    coarseBMatrixNorm R (Jc.chart z r hr a z r) ≤ mhigh ∧
      coarseSigmaStarInvMatrixNorm R (Jc.chart z r hr a z r) ≤ mlow⁻¹ :=
  aux_lem_as_coarse_scalar_cell_bridge_chart Jc z r hr a hmlow hbd R
    (Homogenization.openCubeSet_subset_of_mem_descendantsAtScale
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) hR)

/-! ## F. The cutoff coefficient -/

/-- Pointwise bounds of `A_N` on the closed root cube are physical a.e. bounds of the
positive coefficient `cutoffPositiveCoefficient` on the open root cube. -/
theorem aux_lem_as_coarse_scalar_cell_bridge_cutoff_ae {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) {mlow mhigh : ℝ}
    (hbd : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      mlow ≤ cutoffCoefficient M H om N x ∧ cutoffCoefficient M H om N x ≤ mhigh) :
    ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      mlow ≤ (cutoffPositiveCoefficient M H om N z hr).val y ∧
        (cutoffPositiveCoefficient M H om N z hr).val y ≤ mhigh := by
  have : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (closedCube z r hr : Set (SpatialCoordinates d))) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have h0 := normalizedContinuousPositiveCoefficient_coeFn
    (Ω := centeredCube z r hr) (closedCube z r hr)
    (cutoffCoefficientCM M H om N z hr) (cutoffCoefficientCM_pos M H om N z hr) 1 one_pos
  filter_upwards [h0, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet]
    with y hy hyU
  have hval : (cutoffPositiveCoefficient M H om N z hr).val y =
      cutoffCoefficient M H om N y := by
    have h := hy hyU
    rw [div_one] at h
    exact h
  rw [hval]
  exact hbd y (centeredCube_subset_closedCube z hr hyU)



theorem aux_lem_as_coarse_scalar_cell_bridge_cutoff {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) {mlow mhigh : ℝ} (hmlow : 0 < mlow)
    (hbd : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      mlow ≤ cutoffCoefficient M H om N x ∧ cutoffCoefficient M H om N x ≤ mhigh) :
    ∀ n : ℕ, ∀ R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (n : ℤ)),
      coarseBMatrixNorm R (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) ≤
          mhigh ∧
        coarseSigmaStarInvMatrixNorm R
            (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) ≤ mlow⁻¹ := by
  have : NeZero d := ⟨by omega⟩
  intro n R hR
  exact aux_lem_as_coarse_scalar_cell_bridge_chart_desc Jc z r hr _ hmlow
    (aux_lem_as_coarse_scalar_cell_bridge_cutoff_ae M H om N z r hr hbd) n R hR



theorem lem_as_coarse_scalar_cell_bridge {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (mlow mhigh : ℕ → BilateralField d → ℝ)
    (hext : ∀ N : ℕ, 0 < mlow N om ∧
      ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        mlow N om ≤ cutoffCoefficient M H om N x ∧ cutoffCoefficient M H om N x ≤ mhigh N om) :
    (∀ N : ℕ, 0 ≤ mhigh N om + (mlow N om)⁻¹) ∧
      ∀ N : ℕ, ∀ n : ℕ, ∀ R ∈ Homogenization.descendantsAtScale
          (Homogenization.originCube d 0) ((Homogenization.originCube d 0).scale - (n : ℤ)),
        coarseBMatrixNorm R
            (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) ≤
            mhigh N om + (mlow N om)⁻¹ ∧
          coarseSigmaStarInvMatrixNorm R
            (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) ≤
            mhigh N om + (mlow N om)⁻¹ := by
  have hz : z ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
    change dist z z ≤ r / 2
    rw [dist_self]
    positivity
  have hle : ∀ N : ℕ, mlow N om ≤ mhigh N om := fun N =>
    ((hext N).2 z hz).1.trans ((hext N).2 z hz).2
  have hinv : ∀ N : ℕ, 0 < (mlow N om)⁻¹ := fun N => inv_pos.2 (hext N).1
  have hhigh : ∀ N : ℕ, 0 < mhigh N om := fun N => (hext N).1.trans_le (hle N)
  refine ⟨fun N => (add_pos (hhigh N) (hinv N)).le, ?_⟩
  intro N n R hR
  obtain ⟨hb, hs⟩ := aux_lem_as_coarse_scalar_cell_bridge_cutoff hd Jc M H om N z r hr (hext N).1
    (hext N).2 n R hR
  exact ⟨hb.trans (le_add_of_nonneg_right (hinv N).le),
    hs.trans (le_add_of_nonneg_left (hhigh N).le)⟩

end SubdiffusiveProcess.Paper
