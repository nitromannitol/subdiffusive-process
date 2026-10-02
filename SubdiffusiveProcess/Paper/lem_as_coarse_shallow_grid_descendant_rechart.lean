import SubdiffusiveProcess.Paper.lem_extension_cell_moment
import Homogenization.Book.Ch02.Theorems.Dilation
import Homogenization.Internal.Ch02.Adapters
import Homogenization.CoarseGraining.Translation
import Mathlib.Tactic

open MeasureTheory SubdiffusiveProcess SubdiffusiveProcess.Lane4 Homogenization Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-! ## A. The Ch02 coarse matrices are functions of the response `J` alone -/

section ResponseDetermined
open Homogenization.Book.Ch02

variable {d : ℕ} {U V : Domain d} {a : CoeffOn U} {b : CoeffOn V}

theorem aux_rechart_sigmaStarInvCoarse_of_responseJ
    (hJ : ∀ p q : Vec d, responseJ U a p q = responseJ V b p q) :
    Book.Ch02.sigmaStarInvCoarse U a = Book.Ch02.sigmaStarInvCoarse V b := by
  ext i j
  by_cases hij : i = j
  · simp [Book.Ch02.sigmaStarInvCoarse, Book.Ch02.sigmaStarInvEntry, hij, hJ]
  · simp [Book.Ch02.sigmaStarInvCoarse, Book.Ch02.sigmaStarInvEntry, hij, hJ]

theorem aux_rechart_kappaCoarse_of_responseJ
    (hJ : ∀ p q : Vec d, responseJ U a p q = responseJ V b p q) :
    Book.Ch02.kappaCoarse U a = Book.Ch02.kappaCoarse V b := by
  have hS : Book.Ch02.sigmaStarCoarse U a = Book.Ch02.sigmaStarCoarse V b := by
    simp [Book.Ch02.sigmaStarCoarse, aux_rechart_sigmaStarInvCoarse_of_responseJ hJ]
  have hK : Book.Ch02.sigmaStarInvKappaCoarse U a = Book.Ch02.sigmaStarInvKappaCoarse V b := by
    ext i j
    simp [Book.Ch02.sigmaStarInvKappaCoarse, Book.Ch02.mixedResponse, hJ]
  simp [Book.Ch02.kappaCoarse, hS, hK]

theorem aux_rechart_sigmaCoarse_of_responseJ
    (hJ : ∀ p q : Vec d, responseJ U a p q = responseJ V b p q) :
    Book.Ch02.sigmaCoarse U a = Book.Ch02.sigmaCoarse V b := by
  have hC : ∀ p : Vec d, Book.Ch02.canonicalSigmaCorrectedResponse U a p =
      Book.Ch02.canonicalSigmaCorrectedResponse V b p := by
    intro p
    simp [Book.Ch02.canonicalSigmaCorrectedResponse, hJ,
      aux_rechart_sigmaStarInvCoarse_of_responseJ hJ,
      aux_rechart_kappaCoarse_of_responseJ hJ]
  ext i j
  by_cases hij : i = j
  · simp [Book.Ch02.sigmaCoarse, Book.Ch02.sigmaEntry, hij, hC]
  · simp [Book.Ch02.sigmaCoarse, Book.Ch02.sigmaEntry, hij, hC]

theorem aux_rechart_coarseMatrices_of_responseJ
    (hJ : ∀ p q : Vec d, responseJ U a p q = responseJ V b p q) :
    Book.Ch02.coarseMatrices U a = Book.Ch02.coarseMatrices V b := by
  ext <;>
    simp [Book.Ch02.coarseMatrices, aux_rechart_sigmaCoarse_of_responseJ hJ,
      aux_rechart_sigmaStarInvCoarse_of_responseJ hJ,
      aux_rechart_kappaCoarse_of_responseJ hJ]

theorem aux_rechart_bCoarse_of_responseJ
    (hJ : ∀ p q : Vec d, responseJ U a p q = responseJ V b p q) :
    Book.Ch02.bCoarse U a = Book.Ch02.bCoarse V b := by
  unfold Book.Ch02.bCoarse
  rw [aux_rechart_coarseMatrices_of_responseJ hJ]

end ResponseDetermined

/-! ## B. The internal response functional only sees the a.e. class on a domain -/

section AEInvariance
open Homogenization.Book.Ch02

/-- A Ch02 coefficient object with a prescribed representative `F`, a.e. equal
on the domain to the representative of `b`. -/
def aux_rechart_coeffOnOfAE {d : ℕ} {U : Domain d} (b : CoeffOn U)
    (F : CoeffField d) (h : F =ᵐ[volumeMeasureOn (U : Set (Vec d))] b.toCoeffField) :
    CoeffOn U where
  toCoeffField := F
  lam := b.lam
  Lam := b.Lam
  lam_pos := b.lam_pos
  lam_le_Lam := b.lam_le_Lam
  aeStronglyMeasurable := by
    intro i j
    refine (b.aeStronglyMeasurable i j).congr ?_
    filter_upwards [h] with x hx
    classical
    by_cases hxU : x ∈ (U : Set (Vec d))
    · simp [restrictCoeffField, hxU, hx]
    · simp [restrictCoeffField, hxU]
  aeElliptic := by
    filter_upwards [h, b.aeElliptic] with x hx hb
    rw [hx]
    exact hb

theorem aux_rechart_ResponseJ_congr_ae {d : ℕ} {U : Domain d} (b : CoeffOn U)
    (F : CoeffField d) (h : F =ᵐ[volumeMeasureOn (U : Set (Vec d))] b.toCoeffField)
    (p q : Vec d) :
    ResponseJ (U : Set (Vec d)) p q F = responseJ U b p q := by
  have hAE : CoeffOn.AEEq (aux_rechart_coeffOnOfAE b F h) b := h
  have h1 := responseJ_eq_ofAEEq hAE p q
  rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ] at h1
  exact h1

end AEInvariance

/-! ## C. Cube geometry: every triadic cube is a translate of a dilated unit cube -/

section Geometry
open Homogenization.Book.Ch02

theorem aux_rechart_openCubeSet_eq_translateSet {d : ℕ} (R : TriadicCube d) :
    openCubeSet R =
      translateSet (cubeCenter R) (openCubeSet (dilateCube R.scale (originCube d 0))) := by
  ext x
  rw [mem_translateSet_iff_sub_mem]
  have hs : cubeScaleFactor (dilateCube R.scale (originCube d 0)) = cubeScaleFactor R := by
    simp [cubeScaleFactor, dilateCube, originCube]
  simp only [openCubeSet, Set.mem_setOf_eq, hs, cubeCenter, Pi.sub_apply]
  simp only [dilateCube_index, originCube, Pi.zero_apply, Int.cast_zero]
  constructor
  · intro h i
    have h1 := h i
    constructor <;> nlinarith [h1.1, h1.2]
  · intro h i
    have h1 := h i
    constructor <;> nlinarith [h1.1, h1.2]

theorem aux_rechart_add_center_mem {d : ℕ} (R : TriadicCube d) {x : Vec d}
    (hx : x ∈ openCubeSet (dilateCube R.scale (originCube d 0))) :
    x + cubeCenter R ∈ openCubeSet R := by
  rw [aux_rechart_openCubeSet_eq_translateSet R]
  exact ⟨x, hx, rfl⟩

theorem aux_rechart_undilate_mem {d : ℕ} (R : TriadicCube d) {x : Vec d}
    (hx : x ∈ openCubeSet (dilateCube R.scale (originCube d 0))) :
    undilateVec R.scale x ∈ openCubeSet (originCube d 0) := by
  rw [openCubeSet_dilateCube] at hx
  rcases hx with ⟨y, hy, rfl⟩
  simpa [undilateVec, smul_smul, triadicDilationFactor_ne_zero R.scale] using hy

end Geometry

/-! ## D. The rechart of the response functional -/

section Rechart
open Homogenization.Book.Ch02

/-- **Descendant rechart of `J`.** Let `a` be a Ch02 coefficient on an arbitrary
triadic cube `R` and `b` one on the unit origin cube. If, for one everywhere
defined matrix field `G`, `a = G` a.e. on `R` and
`b(y) = G(c_R + 3^{scale R} y)` a.e. on the origin cube (i.e. `b` is `a` read in
the affine chart of `R`), the two response functionals coincide. -/
theorem aux_rechart_responseJ_eq {d : ℕ} {R : TriadicCube d}
    (a : CoeffOn (cubeDomain R)) (b : CoeffOn (cubeDomain (originCube d 0)))
    (G : Vec d → Mat d)
    (hA : a.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet R)] G)
    (hB : b.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet (originCube d 0))]
      fun y => G (cubeCenter R + cubeScaleFactor R • y))
    (p q : Vec d) :
    responseJ (cubeDomain R) a p q = responseJ (cubeDomain (originCube d 0)) b p q := by
  let s : ℤ := R.scale
  let R0 : TriadicCube d := dilateCube s (originCube d 0)
  let c : Vec d := cubeCenter R
  let b' : CoeffOn (cubeDomain R0) := CoeffOn.dilate s b
  have hb' : CoeffOn.IsCubeDilation s b b' := CoeffOn.dilate_isCubeDilation s b
  have hmeasR : MeasurableSet (openCubeSet R) := Homogenization.measurableSet_openCubeSet R
  have hmeas0 : MeasurableSet (openCubeSet (originCube d 0)) :=
    Homogenization.measurableSet_openCubeSet _
  have hmeasR0 : MeasurableSet (openCubeSet R0) := Homogenization.measurableSet_openCubeSet _
  have hAt : translateCoeffField c a.toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet R0)] fun x => G (x + c) := by
    have h0 : ∀ᵐ y ∂(volume : Measure (Vec d)), y ∈ openCubeSet R →
        a.toCoeffField y = G y := (ae_restrict_iff' hmeasR).1 hA
    have h1 : ∀ᵐ x ∂(volume : Measure (Vec d)), x + c ∈ openCubeSet R →
        a.toCoeffField (x + c) = G (x + c) :=
      (measurePreserving_add_right (volume : Measure (Vec d)) c).quasiMeasurePreserving.ae h0
    refine (ae_restrict_iff' hmeasR0).2 ?_
    filter_upwards [h1] with x hx hxR0
    exact hx (aux_rechart_add_center_mem R hxR0)
  have hBd : b'.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet R0)] fun x => G (x + c) := by
    have h0 : ∀ᵐ y ∂(volume : Measure (Vec d)), y ∈ openCubeSet (originCube d 0) →
        b.toCoeffField y = G (c + cubeScaleFactor R • y) := (ae_restrict_iff' hmeas0).1 hB
    have hq : Measure.QuasiMeasurePreserving (fun x : Vec d => undilateVec s x)
        volume volume := by
      simpa [undilateVec] using
        (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
          (inv_ne_zero (triadicDilationFactor_ne_zero s)))
    have h1 : ∀ᵐ x ∂(volume : Measure (Vec d)),
        undilateVec s x ∈ openCubeSet (originCube d 0) →
          b.toCoeffField (undilateVec s x) =
            G (c + cubeScaleFactor R • undilateVec s x) := hq.ae h0
    have h2 : dilateCoeffField s b.toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet R0)] fun x => G (x + c) := by
      refine (ae_restrict_iff' hmeasR0).2 ?_
      filter_upwards [h1] with x hx hxR0
      have hxu := hx (aux_rechart_undilate_mem R hxR0)
      rw [dilateCoeffField_apply, hxu]
      congr 1
      have hsc : cubeScaleFactor R • undilateVec s x = x := by
        have h3 : (3 : ℝ) ^ R.scale ≠ 0 := zpow_ne_zero _ (by norm_num)
        simp [undilateVec, smul_smul, cubeScaleFactor, triadicDilationFactor, s, h3]
      rw [hsc, add_comm]
    exact hb'.coeff_ae_eq.trans h2
  have hF : translateCoeffField c a.toCoeffField
      =ᵐ[volumeMeasureOn ((cubeDomain R0 : Domain d) : Set (Vec d))] b'.toCoeffField := by
    simpa only [cubeDomain_coe] using hAt.trans hBd.symm
  calc
    responseJ (cubeDomain R) a p q = ResponseJ (openCubeSet R) p q a.toCoeffField := by
      rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ, cubeDomain_coe]
    _ = ResponseJ (translateSet c (openCubeSet R0)) p q a.toCoeffField := by
      rw [← aux_rechart_openCubeSet_eq_translateSet R]
    _ = ResponseJ (openCubeSet R0) p q (translateCoeffField c a.toCoeffField) :=
      ResponseJ_translateSet_eq_translateCoeffField c _ p q _
    _ = responseJ (cubeDomain R0) b' p q := by
      have h := aux_rechart_ResponseJ_congr_ae b' _ hF p q
      rwa [cubeDomain_coe] at h
    _ = responseJ (cubeDomain (originCube d 0)) b p q := responseJ_dilate hb' p q

theorem aux_rechart_matrices_eq {d : ℕ} {R : TriadicCube d}
    (a : CoeffOn (cubeDomain R)) (b : CoeffOn (cubeDomain (originCube d 0)))
    (G : Vec d → Mat d)
    (hA : a.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet R)] G)
    (hB : b.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet (originCube d 0))]
      fun y => G (cubeCenter R + cubeScaleFactor R • y)) :
    Book.Ch02.bCoarse (cubeDomain R) a = Book.Ch02.bCoarse (cubeDomain (originCube d 0)) b ∧
      Book.Ch02.sigmaStarInvCoarse (cubeDomain R) a =
        Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d 0)) b := by
  have hJ := aux_rechart_responseJ_eq a b G hA hB
  exact ⟨aux_rechart_bCoarse_of_responseJ hJ,
    aux_rechart_sigmaStarInvCoarse_of_responseJ hJ⟩

end Rechart

/-! ## E. The actual shallow-grid descendant rechart -/

section Shallow
open Homogenization.Book.Ch02

theorem aux_rechart_descendant_facts {d : ℕ} (k : ℕ) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) (-(k : ℤ))) :
    openCubeSet R ⊆ openCubeSet (originCube d 0) ∧ R.scale = -(k : ℤ) := by
  have hk : (-(k : ℤ)) ≤ (originCube d 0).scale := by simp [originCube]
  refine ⟨?_, ?_⟩
  · have hR' := hR
    rw [descendantsAtScale_eq_descendantsAtDepth _ hk] at hR'
    exact openCubeSet_subset_of_mem_descendantsAtDepth hR'
  · have h := scale_eq_sub_of_mem_descendantsAtScale hk hR
    simpa [originCube] using h

theorem aux_rechart_actual_descendant_core {d : ℕ}
    (Jc : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N k : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : TriadicCube d) (hR : R ∈ descendantsAtScale (originCube d 0) (-(k : ℤ)))
    (w : SpatialCoordinates d) (ρ : ℝ) (hρpos : 0 < ρ)
    (hw : w = fun i => z i + r * cubeCenter R i) (hρ : ρ = r * (3 : ℝ) ^ (-(k : ℤ))) :
    Book.Ch02.bCoarse (cubeDomain R)
        ((Jc.chart z r hr (cutoffPositiveCoefficient M H omega N z hr) z r).coeffOn R) =
      Book.Ch02.bCoarse (cubeDomain (originCube d 0))
        ((Jc.chart w ρ hρpos (cutoffPositiveCoefficient M H omega N w hρpos) w ρ).coeffOn
          (originCube d 0)) ∧
    Book.Ch02.sigmaStarInvCoarse (cubeDomain R)
        ((Jc.chart z r hr (cutoffPositiveCoefficient M H omega N z hr) z r).coeffOn R) =
      Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d 0))
        ((Jc.chart w ρ hρpos (cutoffPositiveCoefficient M H omega N w hρpos) w ρ).coeffOn
          (originCube d 0)) := by
  have hfacts := aux_rechart_descendant_facts k hR
  let G : Vec d → Mat d := fun x =>
    scalarMatrix (cutoffCoefficient M H omega N (fun i => z i + r * x i))
  have hA := aux_lem_extension_cell_moment_chart_scalar_identity Jc M H omega N z r hr z r hr
    subset_rfl R hfacts.1
  have hB0 := aux_lem_extension_cell_moment_chart_scalar_identity Jc M H omega N w ρ hρpos
    w ρ hρpos subset_rfl (originCube d 0) subset_rfl
  have hB : ((Jc.chart w ρ hρpos (cutoffPositiveCoefficient M H omega N w hρpos) w ρ).coeffOn
      (originCube d 0)).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d 0))]
        fun y => G (cubeCenter R + cubeScaleFactor R • y) := by
    filter_upwards [hB0] with y hy
    refine hy.trans ?_
    have hpt : (fun i => w i + ρ * y i) =
        (fun i => z i + r * (cubeCenter R + cubeScaleFactor R • y) i) := by
      funext i
      rw [hw, hρ]
      simp only [cubeScaleFactor, hfacts.2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [G, hpt]
  exact aux_rechart_matrices_eq _ _ G hA hB

/-- Actual parent-chart descendant rechart: the `bCoarse` and inverse-star
matrices, and their operator norms, agree exactly with those of the actual
cell chart on the unit origin cube. -/
theorem lem_as_coarse_shallow_grid_descendant_rechart {d : ℕ}
    (Jc : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N k : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : TriadicCube d) (hR : R ∈ descendantsAtScale (originCube d 0) (-(k : ℤ))) :
    let w : SpatialCoordinates d := fun i => z i + r * cubeCenter R i
    let ρ : ℝ := r * (3 : ℝ) ^ (-(k : ℤ))
    let A : TriadicCoeffFamily d :=
      Jc.chart z r hr (cutoffPositiveCoefficient M H omega N z hr) z r
    let B : TriadicCoeffFamily d :=
      Jc.chart w ρ (mul_pos hr (by positivity))
        (cutoffPositiveCoefficient M H omega N w (mul_pos hr (by positivity))) w ρ
    Book.Ch02.bCoarse (cubeDomain R) (A.coeffOn R) =
        Book.Ch02.bCoarse (cubeDomain (originCube d 0)) (B.coeffOn (originCube d 0)) ∧
      Book.Ch02.sigmaStarInvCoarse (cubeDomain R) (A.coeffOn R) =
        Book.Ch02.sigmaStarInvCoarse (cubeDomain (originCube d 0))
          (B.coeffOn (originCube d 0)) ∧
      coarseBMatrixNorm R A = coarseBMatrixNorm (originCube d 0) B ∧
      coarseSigmaStarInvMatrixNorm R A = coarseSigmaStarInvMatrixNorm (originCube d 0) B := by
  intro w ρ A B
  have hm := aux_rechart_actual_descendant_core Jc M H omega N k z r hr R hR w ρ
    (mul_pos hr (by positivity)) rfl rfl
  refine ⟨hm.1, hm.2, ?_, ?_⟩
  · unfold coarseBMatrixNorm
    exact congrArg matrixNorm hm.1
  · unfold coarseSigmaStarInvMatrixNorm
    exact congrArg matrixNorm hm.2

theorem aux_rechart_unit_descendant {d : ℕ}
    (Jc : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N k : ℕ)
    (z : SpatialCoordinates d) (hr : (0 : ℝ) < 1)
    (R : TriadicCube d) (hR : R ∈ descendantsAtScale (originCube d 0) (-(k : ℤ))) :
    let w : SpatialCoordinates d := fun i => z i + cubeCenter R i
    let A : TriadicCoeffFamily d :=
      Jc.chart z 1 hr (cutoffPositiveCoefficient M H omega N z hr) z 1
    let B : TriadicCoeffFamily d :=
      Jc.chart w ((3 : ℝ)^(-(k : ℤ))) (by positivity)
        (cutoffPositiveCoefficient M H omega N w (by positivity)) w ((3 : ℝ)^(-(k : ℤ)))
    coarseBMatrixNorm R A = coarseBMatrixNorm (originCube d 0) B ∧
      coarseSigmaStarInvMatrixNorm R A = coarseSigmaStarInvMatrixNorm (originCube d 0) B := by
  intro w A B
  have hm := aux_rechart_actual_descendant_core Jc M H omega N k z 1 hr R hR w
    ((3 : ℝ)^(-(k : ℤ))) (by positivity) (by funext i; simp [w]) (one_mul _).symm
  refine ⟨?_, ?_⟩
  · unfold coarseBMatrixNorm
    exact congrArg matrixNorm hm.1
  · unfold coarseSigmaStarInvMatrixNorm
    exact congrArg matrixNorm hm.2

end Shallow

end Paper









