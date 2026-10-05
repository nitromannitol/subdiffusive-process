module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_charted_cellMap_ae
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_cell_coefficient_comparison
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_cellMap_mem_osc_ball
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_affine_coeff_comparison
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_matched_limit_affine_moment
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity Homogenization Set
open TopologicalSpace
open scoped NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-! ## A. Scalar positive coefficients on the unit origin cube -/

/-- The unit centred cube is the open origin triadic cube. -/
theorem aux_chart_transfer_root_carrier {d : ℕ} :
    (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
      Set (SpatialCoordinates d)) = openCubeSet (originCube d 0) := by
  simpa using _root_.SubdiffusiveProcess.EllipticRegularity.centeredCube_zero_eq_openCubeSet_originCube
    (d := d) 0 (by norm_num)

theorem aux_chart_transfer_root_volume {d : ℕ} :
    volume.real (centeredCube (0 : SpatialCoordinates d) 1
      (by norm_num) : Set (SpatialCoordinates d)) = 1 := by
  rw [Measure.real, centeredCube_volume]
  simp

/-- A continuous, everywhere positive scalar field, packaged as a positive
coefficient on the unit origin cube. -/
def aux_chart_transfer_rootCoeff {d : ℕ} (f : SpatialCoordinates d → ℝ)
    (hf : Continuous f) (hpos : ∀ x, 0 < f x) :
    PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)) :=
  @normalizedContinuousPositiveCoefficient d
    (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num))
    (closedCube (0 : SpatialCoordinates d) 1 (by norm_num))
    ⟨centeredCube_subset_closedCube (0 : SpatialCoordinates d) (by norm_num)⟩
    ⟨fun x => f x, hf.comp continuous_subtype_val⟩ (fun x => hpos x) 1 one_pos

theorem aux_chart_transfer_rootCoeff_ae {d : ℕ} (f : SpatialCoordinates d → ℝ)
    (hf : Continuous f) (hpos : ∀ x, 0 < f x) :
    ((aux_chart_transfer_rootCoeff f hf hpos).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube (0 : SpatialCoordinates d) 1
        (by norm_num) : Set (SpatialCoordinates d))] f := by
  let Om := centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let K := closedCube (0 : SpatialCoordinates d) 1 (by norm_num)
  have : Fact ((Om : Set (SpatialCoordinates d)) ⊆ K) :=
    ⟨centeredCube_subset_closedCube (0 : SpatialCoordinates d) (by norm_num)⟩
  have h0 := normalizedContinuousPositiveCoefficient_coeFn (Ω := Om) K
    ⟨fun x => f x, hf.comp continuous_subtype_val⟩ (fun x => hpos x) 1 one_pos
  filter_upwards [h0, ae_restrict_mem Om.isOpen.measurableSet] with x hx hxOm
  have h := hx hxOm
  rw [div_one] at h
  exact h

/-! ## B. Ch02 values on a domain carried by an open set -/

theorem aux_chart_transfer_dirichletNu {d : ℕ}
    (U : Homogenization.Book.Ch02.Domain d) (Om : Opens (SpatialCoordinates d))
    [IsFiniteMeasure (volume.restrict (Om : Set (SpatialCoordinates d)))]
    (hset : (Om : Set (SpatialCoordinates d)) = (U : Set (Homogenization.Vec d)))
    {a : Homogenization.Vec d → ℝ}
    (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U a)
    (hOm : Bornology.IsBounded (Om : Set (SpatialCoordinates d)))
    (hvol : 0 < volume.real (Om : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Om,
      ‖(w : SobolevData Om).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Om) w‖)
    (aP : PositiveCoefficient Om)
    (haP : ((aP.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] a))
    (p : Fin d → ℝ) :
    Homogenization.Book.Ch02.symmetricDirichletNu U data.toCoeffOn p =
      affineDirichletResponse hOm hD aP p /
        (2 * volume.real (Om : Set (SpatialCoordinates d))) := by
  obtain ⟨Uc, hUdom, hUne⟩ := U
  simp only at hset data ⊢
  subst hset
  exact symmetricDirichletNu_eq_affineDirichletResponse hUdom hUne data hOm hD aP haP hvol p

theorem aux_chart_transfer_neumannNu {d : ℕ}
    (U : Homogenization.Book.Ch02.Domain d) (Om : Opens (SpatialCoordinates d))
    [IsFiniteMeasure (volume.restrict (Om : Set (SpatialCoordinates d)))]
    (hset : (Om : Set (SpatialCoordinates d)) = (U : Set (Homogenization.Vec d)))
    {a : Homogenization.Vec d → ℝ}
    (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U a)
    (hvol : 0 < volume.real (Om : Set (SpatialCoordinates d)))
    (hN : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph Om,
      ‖(w : SobolevData Om).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Om) w‖)
    (aP : PositiveCoefficient Om)
    (haP : ((aP.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] a))
    (q : Fin d → ℝ) :
    Homogenization.Book.Ch02.symmetricNeumannNu U data.toCoeffOn q =
      affineInverseNeumannResponse hN aP q /
        (2 * volume.real (Om : Set (SpatialCoordinates d))) := by
  obtain ⟨Uc, hUdom, hUne⟩ := U
  simp only at hset data ⊢
  subst hset
  exact symmetricNeumannNu_eq_affineInverseNeumannResponse hUdom hUne data hN aP haP hvol q

/-! ## C. Diagonal traces of the symmetric Ch02 matrices -/

section Trace
open Homogenization.Book.Ch02

theorem aux_chart_transfer_b_trace {d : ℕ} (U : Domain d) (A : CoeffOn U)
    (hs : CoeffOn.IsSymmetric A) :
    matrixNorm (bCoarse U A) ≤
      ∑ i : Fin d, 2 * symmetricDirichletNu U A (Pi.single i 1) := by
  have ht := responseSymmetricDirichletNeumannTheory U A hs
  have hb : bCoarse U A = Book.Ch02.sigmaCoarse U A := ht.derived_matrices.2.2
  calc
    matrixNorm (bCoarse U A) ≤ Matrix.trace (bCoarse U A) :=
      matrixNorm_le_trace_of_posSemidef _ (bCoarse_posSemidef U A)
    _ = ∑ i : Fin d, 2 * symmetricDirichletNu U A (Pi.single i 1) := by
      rw [hb]
      apply Finset.sum_congr rfl
      intro i _
      rw [ht.dirichlet_value_by_sigma]
      have hdiag : vecDot (Pi.single i (1 : ℝ))
          (matVecMul (Book.Ch02.sigmaCoarse U A) (Pi.single i 1)) =
            Book.Ch02.sigmaCoarse U A i i := by
        simp [vecDot, matVecMul, Pi.single_apply]
      rw [hdiag, Matrix.diag_apply]
      ring

theorem aux_chart_transfer_star_trace {d : ℕ} (U : Domain d) (A : CoeffOn U)
    (hs : CoeffOn.IsSymmetric A) :
    matrixNorm (Book.Ch02.sigmaStarInvCoarse U A) ≤
      ∑ i : Fin d, 2 * symmetricNeumannNu U A (Pi.single i 1) := by
  have ht := responseSymmetricDirichletNeumannTheory U A hs
  calc
    matrixNorm (Book.Ch02.sigmaStarInvCoarse U A) ≤
        Matrix.trace (Book.Ch02.sigmaStarInvCoarse U A) :=
      matrixNorm_le_trace_of_posSemidef _ (sigmaStarInvCoarse_posDef U A).posSemidef
    _ = ∑ i : Fin d, 2 * symmetricNeumannNu U A (Pi.single i 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [ht.neumann_value_by_sigmaStarInv]
      have hdiag : vecDot (Pi.single i (1 : ℝ))
          (matVecMul (Book.Ch02.sigmaStarInvCoarse U A) (Pi.single i 1)) =
          Book.Ch02.sigmaStarInvCoarse U A i i := by
        simp [vecDot, matVecMul, Pi.single_apply]
      rw [hdiag, Matrix.diag_apply]
      ring

end Trace

/-! ## D. Origin-cube Ch02 values of an a.e. scalar coefficient -/

section Chart
open Homogenization.Book.Ch02

/-- If a Ch02 coefficient on the origin cube is a.e. the scalar matrix of a
continuous positive field `f`, its symmetric Dirichlet and Neumann values are
half the affine Sobolev responses of the packaged positive coefficient of `f`
on the unit centred cube (which has volume one). -/
theorem aux_chart_transfer_scalar_nu {d : ℕ} [NeZero d]
    (A : CoeffOn (cubeDomain (originCube d 0)))
    (f : SpatialCoordinates d → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    (hA : ∀ᵐ y ∂volumeMeasureOn (openCubeSet (originCube d 0)),
      A.toCoeffField y = scalarMatrix (f y)) (p : Fin d → ℝ) :
    symmetricDirichletNu (cubeDomain (originCube d 0)) A p =
        affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d)
          (by norm_num : (0 : ℝ) < 1)) (aux_matched_root_poincare (d := d)).1
          (aux_chart_transfer_rootCoeff f hf hpos) p / 2 ∧
      symmetricNeumannNu (cubeDomain (originCube d 0)) A p =
        affineInverseNeumannResponse (aux_matched_root_poincare (d := d)).2
          (aux_chart_transfer_rootCoeff f hf hpos) p / 2 := by
  let U := cubeDomain (originCube d 0)
  let Om := centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let data := Classical.choice
    (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos
      hf hpos U)
  have hset : (Om : Set (SpatialCoordinates d)) = (U : Set (Homogenization.Vec d)) := by
    simpa only [U, cubeDomain_coe] using (aux_chart_transfer_root_carrier (d := d))
  have hAE : CoeffOn.AEEq A data.toCoeffOn := by
    unfold CoeffOn.AEEq
    simpa only [U, cubeDomain_coe, SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData.toCoeffOn,
      SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField] using! hA
  have hvol : 0 < volume.real (Om : Set (SpatialCoordinates d)) := by
    rw [aux_chart_transfer_root_volume]
    norm_num
  have hbQ := aux_chart_transfer_rootCoeff_ae f hf hpos
  have hv : volume.real (Om : Set (SpatialCoordinates d)) = 1 :=
    aux_chart_transfer_root_volume
  have hDir := aux_chart_transfer_dirichletNu U Om hset data
    (centeredCube_isBounded (0 : SpatialCoordinates d) (by norm_num)) hvol
    (aux_matched_root_poincare (d := d)).1 _ hbQ p
  have hNeu := aux_chart_transfer_neumannNu U Om hset data hvol
    (aux_matched_root_poincare (d := d)).2 _ hbQ p
  refine ⟨(symmetricDirichletNu_eq_ofAEEq hAE p).trans (hDir.trans ?_),
    (symmetricNeumannNu_eq_ofAEEq hAE p).trans (hNeu.trans ?_)⟩
  · exact congrArg _ (by rw [hv, mul_one])
  · exact congrArg _ (by rw [hv, mul_one])

end Chart

/-! ## E. The actual retained cell against the shifted `H = 0` coefficient -/

/-- The actual cutoff coefficient of the cell `w + 3^{-k} Q_0`, read in the
cell chart on the origin cube. -/
def aux_chart_transfer_cellCoeff {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (ω : BilateralField d)
    (N k : ℕ) (w : SpatialCoordinates d) : SpatialCoordinates d → ℝ :=
  fun y => cutoffCoefficient M H ω N (aux_lem_as_coarse_shallow_grid_cellMap k w y)

theorem aux_chart_transfer_cellCoeff_continuous {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (ω : BilateralField d)
    (N k : ℕ) (w : SpatialCoordinates d) :
    Continuous (aux_chart_transfer_cellCoeff M H ω N k w) :=
  (cutoffCoefficient_continuous M H ω N).comp
    (aux_lem_as_coarse_shallow_grid_cellMap k w).continuous

theorem aux_chart_transfer_cellCoeff_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (ω : BilateralField d)
    (N k : ℕ) (w : SpatialCoordinates d) (y : SpatialCoordinates d) :
    0 < aux_chart_transfer_cellCoeff M H ω N k w y :=
  cutoffCoefficient_pos M H ω N _

/-- The positive coefficient on the unit cube carrying the actual cell
coefficient. -/
def aux_chart_transfer_cellPos {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (ω : BilateralField d)
    (N k : ℕ) (w : SpatialCoordinates d) :
    PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)) :=
  aux_chart_transfer_rootCoeff (aux_chart_transfer_cellCoeff M H ω N k w)
    (aux_chart_transfer_cellCoeff_continuous M H ω N k w)
    (aux_chart_transfer_cellCoeff_pos M H ω N k w)

/-- The shifted infrared-free coefficient `A^{0,Θ_{k,w}ω}_{N-k}` on the unit
cube: the coefficient of the matched unit response bank. -/
def aux_chart_transfer_shiftedPos {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (ω : BilateralField d) (N k : ℕ) (w : SpatialCoordinates d) :
    PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)) :=
  cutoffPositiveCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
    (aux_lem_as_coarse_shallow_grid_scaleShift k w ω) (N - k)
    (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1)

/-- Two-sided a.e. comparison of the two positive coefficients on the unit cube:
exact coarse factor times the shifted `H = 0` coefficient, up to `e^{±osc}`. -/
theorem aux_chart_transfer_coefficient_bounds {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ω : BilateralField d) (N k : ℕ) (hk : k ≤ N) (w : SpatialCoordinates d) :
    let g : C(SpatialCoordinates d, ℝ) :=
      H ω + ∑ j ∈ Finset.range k, ω (-(j : ℤ))
    let osc : ℝ := sSup {v : ℝ | ∃ x ∈ Metric.closedBall w
      (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)),
      ∃ x' ∈ Metric.closedBall w (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)),
        v = |g x - g x'|}
    let s : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
        Real.exp (g w - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
    ∀ᵐ y ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1
        (by norm_num) : Set (SpatialCoordinates d)),
      (s * Real.exp (-osc)) * (aux_chart_transfer_shiftedPos M ω N k w).val y ≤
          (aux_chart_transfer_cellPos M H ω N k w).val y ∧
        (aux_chart_transfer_cellPos M H ω N k w).val y ≤
          (s * Real.exp osc) * (aux_chart_transfer_shiftedPos M ω N k w).val y := by
  intro g osc s
  have hcmp : ∀ᵐ y ∂volume.restrict (openCubeSet (originCube d 0)),
      (s * Real.exp (-osc)) * cutoffCoefficient M
          (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
          (aux_lem_as_coarse_shallow_grid_scaleShift k w ω) (N - k) y ≤
          aux_chart_transfer_cellCoeff M H ω N k w y ∧
        aux_chart_transfer_cellCoeff M H ω N k w y ≤
          (s * Real.exp osc) * cutoffCoefficient M
            (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
            (aux_lem_as_coarse_shallow_grid_scaleShift k w ω) (N - k) y := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet (originCube d 0))] with y hy
    exact lem_as_coarse_shallow_grid_actual_cell_coefficient_comparison M H ω N k hk w y
      (lem_as_coarse_shallow_grid_cellMap_mem_osc_ball (k := k) w y hy)
  rw [← aux_chart_transfer_root_carrier] at hcmp
  filter_upwards [hcmp,
    aux_matched_physical_positive_coeff_ae M (N - k)
      (aux_lem_as_coarse_shallow_grid_scaleShift k w ω),
    aux_chart_transfer_rootCoeff_ae (aux_chart_transfer_cellCoeff M H ω N k w)
      (aux_chart_transfer_cellCoeff_continuous M H ω N k w)
      (aux_chart_transfer_cellCoeff_pos M H ω N k w)] with y h ha hb
  simp only [aux_chart_transfer_shiftedPos, aux_chart_transfer_cellPos]
  rw [ha, hb]
  exact h

section Main
open Homogenization.Book.Ch02

/-- **Retained-cell response transfer.** For the actual `in_J` chart of the
actual cutoff coefficient `A_N` (infrared field `H`, sample `ω`) on the cell
of centre `w` and side `3^{-k}`, `k ≤ N`, both Ch02 coarse matrix norms on the
origin cube are bounded by the coarse factor `s e^{±osc}` times the matched
unit response bank of the shifted infrared-free coefficient
`A^{0,Θ_{k,w}ω}_{N-k}`: Dirichlet coordinates for `|b|`, inverse-Neumann
coordinates for `|σ_*^{-1}|`. -/
theorem lem_as_coarse_shallow_grid_chart_response_transfer {d : ℕ} [NeZero d]
    (Jc : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ω : BilateralField d) (N k : ℕ) (hk : k ≤ N) (w : SpatialCoordinates d) :
    let g : C(SpatialCoordinates d, ℝ) :=
      H ω + ∑ j ∈ Finset.range k, ω (-(j : ℤ))
    let osc : ℝ := sSup {v : ℝ | ∃ x ∈ Metric.closedBall w
      (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)),
      ∃ x' ∈ Metric.closedBall w (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)),
        v = |g x - g x'|}
    let s : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
        Real.exp (g w - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
    let A : TriadicCoeffFamily d :=
      Jc.chart w ((3 : ℝ)^(-(k : ℤ))) (by positivity)
        (cutoffPositiveCoefficient M H ω N w (by positivity)) w ((3 : ℝ)^(-(k : ℤ)))
    coarseBMatrixNorm (originCube d 0) A ≤
        (s * Real.exp osc) * ∑ i : Fin d,
          aux_matched_affine_finite_response M (Pi.single i 1) false (N - k)
            (aux_lem_as_coarse_shallow_grid_scaleShift k w ω) ∧
      coarseSigmaStarInvMatrixNorm (originCube d 0) A ≤
        (s * Real.exp (-osc))⁻¹ * ∑ i : Fin d,
          aux_matched_affine_finite_response M (Pi.single i 1) true (N - k)
            (aux_lem_as_coarse_shallow_grid_scaleShift k w ω) := by
  intro g osc s A
  have hA : ∀ᵐ y ∂volumeMeasureOn (openCubeSet (originCube d 0)),
      (A.coeffOn (originCube d 0)).toCoeffField y =
        scalarMatrix (aux_chart_transfer_cellCoeff M H ω N k w y) :=
    lem_as_coarse_shallow_grid_charted_cellMap_ae Jc M H ω N k w
  have hsym : CoeffOn.IsSymmetric (A.coeffOn (originCube d 0)) := by
    unfold CoeffOn.IsSymmetric
    filter_upwards [hA] with y hy
    rw [hy]
    exact scalarMatrix_isSymm _
  have hnu := aux_chart_transfer_scalar_nu (A.coeffOn (originCube d 0))
    (aux_chart_transfer_cellCoeff M H ω N k w)
    (aux_chart_transfer_cellCoeff_continuous M H ω N k w)
    (aux_chart_transfer_cellCoeff_pos M H ω N k w) hA
  have hs : 0 < s :=
    mul_pos (div_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N - k))
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)
  have hL : 0 < s * Real.exp (-osc) := mul_pos hs (Real.exp_pos _)
  have hU : 0 < s * Real.exp osc := mul_pos hs (Real.exp_pos _)
  have hbounds : ∀ᵐ y ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1
      (by norm_num) : Set (SpatialCoordinates d)),
      (s * Real.exp (-osc)) * (aux_chart_transfer_shiftedPos M ω N k w).val y ≤
          (aux_chart_transfer_cellPos M H ω N k w).val y ∧
        (aux_chart_transfer_cellPos M H ω N k w).val y ≤
          (s * Real.exp osc) * (aux_chart_transfer_shiftedPos M ω N k w).val y :=
    aux_chart_transfer_coefficient_bounds M H ω N k hk w
  have hcmp := fun e : Fin d → ℝ =>
    lem_as_coarse_shallow_grid_affine_coeff_comparison
      (centeredCube_isBounded (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1))
      (aux_matched_root_poincare (d := d)).1 (aux_matched_root_poincare (d := d)).2
      (aux_chart_transfer_shiftedPos M ω N k w) (aux_chart_transfer_cellPos M H ω N k w)
      (s * Real.exp (-osc)) (s * Real.exp osc) hL hU
      (hbounds.mono fun y hy => hy.1) (hbounds.mono fun y hy => hy.2) e
  have hB1 : coarseBMatrixNorm (originCube d 0) A ≤
      ∑ i : Fin d, 2 * symmetricDirichletNu (cubeDomain (originCube d 0))
        (A.coeffOn (originCube d 0)) (Pi.single i 1) :=
    aux_chart_transfer_b_trace _ _ hsym
  have hS1 : coarseSigmaStarInvMatrixNorm (originCube d 0) A ≤
      ∑ i : Fin d, 2 * symmetricNeumannNu (cubeDomain (originCube d 0))
        (A.coeffOn (originCube d 0)) (Pi.single i 1) :=
    aux_chart_transfer_star_trace _ _ hsym
  have hB2 : ∀ i : Fin d, 2 * symmetricDirichletNu (cubeDomain (originCube d 0))
        (A.coeffOn (originCube d 0)) (Pi.single i 1) ≤
      (s * Real.exp osc) * aux_matched_affine_finite_response M (Pi.single i 1) false
        (N - k) (aux_lem_as_coarse_shallow_grid_scaleShift k w ω) := by
    intro i
    rw [(hnu (Pi.single i 1)).1]
    have h := (hcmp (Pi.single i 1)).1
    simp only [aux_chart_transfer_cellPos] at h
    simp only [aux_matched_affine_finite_response, aux_chart_transfer_shiftedPos,
      Bool.false_eq_true, ite_false] at h ⊢
    linarith
  have hS2 : ∀ i : Fin d, 2 * symmetricNeumannNu (cubeDomain (originCube d 0))
        (A.coeffOn (originCube d 0)) (Pi.single i 1) ≤
      (s * Real.exp (-osc))⁻¹ * aux_matched_affine_finite_response M (Pi.single i 1) true
        (N - k) (aux_lem_as_coarse_shallow_grid_scaleShift k w ω) := by
    intro i
    rw [(hnu (Pi.single i 1)).2]
    have h := (hcmp (Pi.single i 1)).2
    simp only [aux_chart_transfer_cellPos] at h
    simp only [aux_matched_affine_finite_response, aux_chart_transfer_shiftedPos,
      ite_true] at h ⊢
    linarith
  refine ⟨hB1.trans ?_, hS1.trans ?_⟩
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hB2 i
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hS2 i

end Main

end SubdiffusiveProcess.Paper
