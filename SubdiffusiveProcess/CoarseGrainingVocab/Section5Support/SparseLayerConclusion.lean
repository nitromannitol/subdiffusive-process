module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerCube

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Homogenization.Book Kuhn MeasureTheory ProbabilityTheory Set
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## The two quadratic forms as normalized continuum minima -/

theorem vecDot_randomAMatrix_eq_layer (M : GMCModel d) (m : ℕ) (U : Ch02.Domain d)
    (omega : PotentialSample d) (p : Vec d) :
    vecDot p (matVecMul (randomAMatrix M m U omega) p) =
      (volume (U : Set (Vec d))).toReal⁻¹ *
        dirichletInfOn (layerCoefficient M (Finset.range (m + 1)) omega)
          (U : Set (Vec d)) p := by
  have hfield : aCutoff M m omega =
      layerCoefficient M (Finset.range (m + 1)) omega :=
    funext fun x => aCutoff_eq_layerCoefficient M m omega x
  rw [randomAMatrix, vecDot_aMatrix_eq_dirichletInfOn
    (aCutoffCoeffOnData M m omega U)
    (fun x => by
      rw [aCutoff_eq_layerCoefficient]
      exact (layerCoefficient_pos M _ omega x).le) p, hfield]

theorem vecDot_randomSparseMatrix_eq_layer (M : GMCModel d) {R : ℕ} (hR : 0 < R)
    (N : ℕ) (U : Ch02.Domain d) (omega : PotentialSample d) (p : Vec d) :
    vecDot p (matVecMul (randomSparseMatrix M R N U omega) p) =
      (volume (U : Set (Vec d))).toReal⁻¹ *
        dirichletInfOn (layerCoefficient M (sparseLayerIndices R N) omega)
          (U : Set (Vec d)) p := by
  have hfield : sparseLayerCoefficient M R N omega =
      layerCoefficient M (sparseLayerIndices R N) omega :=
    funext fun x => sparseLayerCoefficient_eq_layerCoefficient M hR N omega x
  rw [vecDot_randomSparseMatrix_eq, hfield]

/-! ## The assembled payload -/



theorem exists_sparse_layer_bound (M : GMCModel d) :
    ∃ q : ℝ, ∃ R : ℕ, 0 < q ∧ q < 1 ∧ 0 < R ∧
      ∀ N : ℕ, ahom M (N * R) ≤ q ^ (N + 1) := by
  classical
  obtain ⟨n0, rfl⟩ : ∃ n0 : ℕ, d = n0 + 1 :=
    ⟨d - 1, by have := M.shellPrefix.dimension; omega⟩
  obtain ⟨R, hRpos, qq, hqq0, hqq1, hqR⟩ := exists_pos_forall_qRCell_lt_one M
  refine ⟨qq, R, hqq0, hqq1, hRpos, fun N => ?_⟩
  set Q : TriadicCube (n0 + 1) := originCube (n0 + 1) ((N * R : ℕ) : ℤ) with hQ
  set U : Ch02.Domain (n0 + 1) := Ch02.cubeDomain Q with hUdef
  set e : Vec (n0 + 1) := Pi.single (0 : Fin (n0 + 1)) (1 : ℝ) with he
  have hUcoe : (U : Set (Vec (n0 + 1))) = openCubeSet Q := rfl
  have hUdom : IsOpenBoundedConvexDomain (openCubeSet Q) :=
    isOpenBoundedConvexDomain_openCubeSet Q
  have hUpos : 0 < (volume (openCubeSet Q)).toReal := volume_toReal_pos U
  -- `ahom` is an infimum over the cube scale
  have hle1 : ahom M (N * R) ≤ abarScalarReadout M (N * R) (N * R) := by
    rw [ahom]
    refine csInf_le ⟨0, ?_⟩ ⟨N * R, rfl⟩
    rintro x ⟨k, rfl⟩
    exact abarScalarReadout_nonneg M _ k
  refine hle1.trans ?_
  rw [abarScalarReadout_eq_integral_vecDot M (N * R) (N * R) (0 : Fin (n0 + 1))]
  -- the comparison with the sparse coefficient
  have hcomp : ∫ omega, vecDot e (matVecMul (randomAMatrix M (N * R) U omega) e)
        ∂M.P.toMeasure ≤
      ∫ omega, vecDot e (matVecMul (randomSparseMatrix M R N U omega) e)
        ∂M.P.toMeasure := by
    simp only [vecDot_randomAMatrix_eq_layer M (N * R) U,
      vecDot_randomSparseMatrix_eq_layer M hRpos N U, hUcoe]
    rw [integral_const_mul, integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact integral_dirichletInfOn_aCutoff_le M hRpos N hUdom (subset_refl _) e
  refine hcomp.trans ?_
  have hcube := integral_vecDot_randomSparseMatrix_cube_le M hRpos hqq0.le hqR N e
  rw [vecNormSq_single, mul_one] at hcube
  exact hcube

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
