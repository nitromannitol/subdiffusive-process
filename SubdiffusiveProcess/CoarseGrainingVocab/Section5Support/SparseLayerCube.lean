import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerInduction




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Homogenization.Book Kuhn MeasureTheory ProbabilityTheory Set
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## The selection of `R`, uniform in the order -/

/-- **`e.strict.decay.qR.gap` with the finite maximum over `mathcal P`.**  There
is a positive spacing `R` and a constant `q_R < 1` dominating the discrete
constant at *every* order simultaneously. -/
theorem exists_pos_forall_qRCell_lt_one (M : GMCModel d) :
    ∃ R : ℕ, 0 < R ∧ ∃ qq : ℝ, 0 < qq ∧ qq < 1 ∧
      ∀ pi : Equiv.Perm (Fin d),
        qRCell M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) ≤ qq := by
  classical
  have hd : 0 < d := lt_of_lt_of_le two_pos M.shellPrefix.dimension
  have hne : (Finset.univ : Finset (Equiv.Perm (Fin d))).Nonempty :=
    Finset.univ_nonempty
  set qs : ℝ := Finset.univ.sup' hne
    (fun pi : Equiv.Perm (Fin d) => qStarCell M (originKuhnCell d pi 0)) with hqs
  have hqs0 : 0 ≤ qs := by
    obtain ⟨pi0, hpi0⟩ := hne
    exact le_trans (qStarCell_nonneg M (originKuhnCell d pi0 0))
      (Finset.le_sup' (fun pi : Equiv.Perm (Fin d) =>
        qStarCell M (originKuhnCell d pi 0)) hpi0)
  have hqs1 : qs < 1 := by
    rw [hqs, Finset.sup'_lt_iff]
    exact fun pi _ => qStarCell_lt_one M (originKuhnCell d pi 0)
  set eps : ℝ := (1 - qs) / 2 with heps'
  have heps : 0 < eps := by rw [heps']; linarith
  have hex : ∀ pi : Equiv.Perm (Fin d), ∃ j : ℤ, j ≤ 0 ∧ ∀ jj ≤ j,
      ∀ r ∈ vecUnitSphere d,
        qRSlope M (unitMesh d jj) (originKuhnCell d pi 0) r ≤
          qStarCell M (originKuhnCell d pi 0) + eps :=
    fun pi => exists_scale_forall_qRSlope_le M rfl heps
  choose j0 hj0le hj0bd using hex
  set j1 : ℤ := Finset.univ.inf' hne j0 with hj1
  obtain ⟨pi0, hpi0⟩ := hne
  have hj1le : j1 ≤ 0 := le_trans (Finset.inf'_le _ hpi0) (hj0le pi0)
  set R : ℕ := (1 - j1).toNat with hR'
  have hRpos : 0 < R := by rw [hR']; omega
  have hRle : ∀ pi : Equiv.Perm (Fin d), -(R : ℤ) ≤ j0 pi := by
    intro pi
    have h : j1 ≤ j0 pi := Finset.inf'_le _ (Finset.mem_univ pi)
    rw [hR']
    omega
  refine ⟨R, hRpos, qs + eps, by linarith, by rw [heps']; linarith, fun pi => ?_⟩
  refine qRCell_le_of_forall M _ _ hd fun r hr => ?_
  have hle := Finset.le_sup' (fun pi : Equiv.Perm (Fin d) =>
    qStarCell M (originKuhnCell d pi 0)) (Finset.mem_univ pi)
  rw [← hqs] at hle
  have hb := hj0bd pi _ (hRle pi) r hr
  linarith

/-! ## The `d!` simplices of a cube -/

theorem cellSup_one (T : KuhnCell d) : cellSup (fun _ : Vec d => (1 : ℝ)) T = 1 := by
  have himg : (fun _ : Vec d => (1 : ℝ)) '' T.closedCarrier = {1} := by
    ext y
    constructor
    · rintro ⟨x, _, rfl⟩
      rfl
    · rintro rfl
      obtain ⟨x, hx⟩ := T.closedCarrier_nonempty
      exact ⟨x, hx, rfl⟩
  rw [cellSup, himg, csSup_singleton]

theorem supportCube_eq_of_mem_selfPartition {Q : TriadicCube d} {T : KuhnCell d}
    (hT : T ∈ triadicSimplexPartition Q Q.scale) : T.supportCube = Q := by
  have h := mem_triadicSimplexPartition_iff.mp hT
  rw [descendantsAtScale_self, Finset.mem_singleton] at h
  exact h

/-- The `d!` Kuhn simplices of a cube cover it and have total volume at most the
cube's. -/
theorem sum_volume_openCarrier_selfPartition_le (Q : TriadicCube d) :
    ∑ T ∈ triadicSimplexPartition Q Q.scale,
      (volume T.openCarrier).toReal ≤ (volume (openCubeSet Q)).toReal := by
  classical
  have hdisj : ((triadicSimplexPartition Q Q.scale : Finset (KuhnCell d)) :
      Set (KuhnCell d)).PairwiseDisjoint KuhnCell.openCarrier :=
    triadicSimplexPartition_openCarrier_pairwiseDisjoint Q Q.scale
  have hmeas : ∀ T : KuhnCell d, MeasurableSet T.openCarrier := fun T =>
    (isOpen_openCarrier T).measurableSet
  have hsum : ∑ T ∈ triadicSimplexPartition Q Q.scale, volume T.openCarrier =
      volume (⋃ T ∈ triadicSimplexPartition Q Q.scale, T.openCarrier) :=
    (measure_biUnion_finset hdisj fun T _ => hmeas T).symm
  have hsub : (⋃ T ∈ triadicSimplexPartition Q Q.scale, T.openCarrier) ⊆
      openCubeSet Q := by
    refine Set.iUnion₂_subset fun T hT => ?_
    have h := T.openCarrier_subset_openCubeSet
    rw [supportCube_eq_of_mem_selfPartition hT] at h
    exact h
  have hle : ∑ T ∈ triadicSimplexPartition Q Q.scale, volume T.openCarrier ≤
      volume (openCubeSet Q) := by
    rw [hsum]
    exact measure_mono hsub
  have htop : volume (openCubeSet Q) ≠ ⊤ :=
    ne_of_lt (isBounded_openCubeSet Q).measure_lt_top
  calc ∑ T ∈ triadicSimplexPartition Q Q.scale, (volume T.openCarrier).toReal
      = (∑ T ∈ triadicSimplexPartition Q Q.scale, volume T.openCarrier).toReal := by
        rw [ENNReal.toReal_sum]
        intro T _
        exact ne_of_lt ((isBounded_openCarrier T).measure_lt_top)
    _ ≤ (volume (openCubeSet Q)).toReal := ENNReal.toReal_mono htop hle



theorem vecDot_randomSparseMatrix_cube_le (M : GMCModel d) (R N : ℕ)
    (p : Vec d) (omega : PotentialSample d) :
    vecDot p (matVecMul (randomSparseMatrix M R N
        (Ch02.cubeDomain (originCube d ((N * R : ℕ) : ℤ))) omega) p) ≤
      ∑ T ∈ triadicSimplexPartition (originCube d ((N * R : ℕ) : ℤ))
          ((N * R : ℕ) : ℤ),
        (volume T.openCarrier).toReal /
            (volume (openCubeSet (originCube d ((N * R : ℕ) : ℤ)))).toReal *
          vecDot p (matVecMul (randomSparseMatrix M R N (kuhnCellDomain T) omega) p) := by
  classical
  set Q : TriadicCube d := originCube d ((N * R : ℕ) : ℤ) with hQ
  have hQscale : Q.scale = ((N * R : ℕ) : ℤ) := rfl
  set S : Finset (KuhnCell d) := triadicSimplexPartition Q Q.scale with hS
  set A : Vec d → ℝ := sparseLayerCoefficient M R N omega with hA'
  have hA : Continuous A := continuous_sparseLayerCoefficient M R N omega
  have hA0 : ∀ x, 0 ≤ A x := fun x => (sparseLayerCoefficient_pos M R N omega x).le
  have hUopen : IsOpen (openCubeSet Q) := isOpen_openCubeSet Q
  have hUb : Bornology.IsBounded (openCubeSet Q) := isBounded_openCubeSet Q
  have hUpos : 0 < (volume (openCubeSet Q)).toReal :=
    volume_toReal_pos (Ch02.cubeDomain Q)
  have hset : ∀ T ∈ S, openCubeSet Q ∩ T.openCarrier = T.openCarrier := by
    intro T hT
    refine Set.inter_eq_self_of_subset_right ?_
    have h := T.openCarrier_subset_openCubeSet
    rw [supportCube_eq_of_mem_selfPartition hT] at h
    exact h
  have hcover : openCubeSet Q ⊆ ⋃ T ∈ (S : Set (KuhnCell d)), T.carrier := by
    intro x hx
    have hxc : x ∈ cubeSet Q := openCubeSet_subset_cubeSet Q hx
    rw [cubeSet_eq_iUnion_triadicSimplexPartition Q (le_refl Q.scale)] at hxc
    exact hxc
  have hmin : ∀ T ∈ S, ∃ w : H10Function (openCubeSet Q ∩ T.openCarrier),
      dirichletEnergyOn' A (openCubeSet Q ∩ T.openCarrier) (p + (0 : KuhnCompetitor
        (openCubeSet Q) S).slope T) w.toH1Function.grad =
        dirichletInfOn A (openCubeSet Q ∩ T.openCarrier)
          (p + (0 : KuhnCompetitor (openCubeSet Q) S).slope T) := by
    intro T hT
    rw [hset T hT]
    exact exists_h10Function_dirichletEnergyOn'_eq_dirichletInfOn
      (sparseLayerCoeffOnData M R N omega (kuhnCellDomain T)) hA0 _
  have hmain := dirichletInfOn_mul_le_sum_cellSup_dirichletInfOn
    (A := A) (B := fun _ : Vec d => (1 : ℝ)) (S := S) (U := openCubeSet Q)
    (s := Q.scale) (p := p) hUopen hUb hA hA0 continuous_const
    (fun _ => zero_le_one)
    (fun T hT => supportCube_scale_eq_of_mem_triadicSimplexPartition
      (le_refl Q.scale) hT)
    hcover 0 hmin
  have hone : (fun x => (1 : ℝ) * A x) = A := by
    funext x
    rw [one_mul]
  rw [hone] at hmain
  have hrhs : ∑ T ∈ S, cellSup (fun _ : Vec d => (1 : ℝ)) T *
        dirichletInfOn A (openCubeSet Q ∩ T.openCarrier)
          (p + (0 : KuhnCompetitor (openCubeSet Q) S).slope T) =
      ∑ T ∈ S, dirichletInfOn A T.openCarrier p := by
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [cellSup_one, one_mul, hset T hT]
    simp
  rw [hrhs] at hmain
  rw [vecDot_randomSparseMatrix_eq, Ch02.cubeDomain_coe]
  have hmul := mul_le_mul_of_nonneg_left hmain
    (show (0 : ℝ) ≤ (volume (openCubeSet Q)).toReal⁻¹ by positivity)
  refine hmul.trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [vecDot_randomSparseMatrix_eq, kuhnCellDomain_coe]
  have hTpos : (volume T.openCarrier).toReal ≠ 0 :=
    ne_of_gt (volume_toReal_pos (kuhnCellDomain T))
  field_simp
  rw [hA']

/-- The sparse bound at a cell of the cube's own partition. -/
theorem integral_vecDot_randomSparseMatrix_cell_le (M : GMCModel d) {R : ℕ}
    (hR : 0 < R) {qq : ℝ} (hqq : 0 ≤ qq)
    (hqR : ∀ pi : Equiv.Perm (Fin d),
      qRCell M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) ≤ qq)
    (N : ℕ) {T : KuhnCell d} (hT : T.supportCube.scale = ((N * R : ℕ) : ℤ))
    (p : Vec d) :
    ∫ omega, vecDot p (matVecMul (randomSparseMatrix M R N
        (kuhnCellDomain T) omega) p) ∂M.P.toMeasure ≤ qq ^ (N + 1) * vecNormSq p := by
  have hTeq : T = dilatedCell (N * R) T.supportCube.index T.order := eq_dilatedCell hT
  rw [hTeq]
  exact sparseLayerBound_pow M hR hqq hqR N _ _ p

/-- **The cube bound in expectation.** -/
theorem integral_vecDot_randomSparseMatrix_cube_le (M : GMCModel d) {R : ℕ}
    (hR : 0 < R) {qq : ℝ} (hqq : 0 ≤ qq)
    (hqR : ∀ pi : Equiv.Perm (Fin d),
      qRCell M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) ≤ qq)
    (N : ℕ) (p : Vec d) :
    ∫ omega, vecDot p (matVecMul (randomSparseMatrix M R N
        (Ch02.cubeDomain (originCube d ((N * R : ℕ) : ℤ))) omega) p)
      ∂M.P.toMeasure ≤ qq ^ (N + 1) * vecNormSq p := by
  classical
  set Q : TriadicCube d := originCube d ((N * R : ℕ) : ℤ) with hQ
  set S : Finset (KuhnCell d) := triadicSimplexPartition Q ((N * R : ℕ) : ℤ) with hS
  have hUpos : 0 < (volume (openCubeSet Q)).toReal :=
    volume_toReal_pos (Ch02.cubeDomain Q)
  have hterm : ∀ T ∈ S, Integrable (fun omega : PotentialSample d =>
      (volume T.openCarrier).toReal / (volume (openCubeSet Q)).toReal *
        vecDot p (matVecMul (randomSparseMatrix M R N (kuhnCellDomain T) omega) p))
      M.P.toMeasure := fun T _ =>
    (integrable_vecDot_randomSparseMatrix M hR N T p).const_mul _
  have hle := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun omega =>
      vecDot_randomSparseMatrix_nonneg M R N
        (Ch02.cubeDomain (originCube d ((N * R : ℕ) : ℤ))) omega p)
    (integrable_finset_sum S hterm)
    (Filter.Eventually.of_forall fun omega =>
      vecDot_randomSparseMatrix_cube_le M R N p omega)
  refine hle.trans ?_
  rw [integral_finset_sum S hterm]
  have hcell : ∀ T ∈ S,
      ∫ omega, (volume T.openCarrier).toReal / (volume (openCubeSet Q)).toReal *
          vecDot p (matVecMul (randomSparseMatrix M R N
            (kuhnCellDomain T) omega) p) ∂M.P.toMeasure ≤
        (volume T.openCarrier).toReal / (volume (openCubeSet Q)).toReal *
          (qq ^ (N + 1) * vecNormSq p) := by
    intro T hT
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hTscale : T.supportCube.scale = ((N * R : ℕ) : ℤ) :=
      supportCube_scale_eq_of_mem_triadicSimplexPartition (le_refl Q.scale) hT
    exact integral_vecDot_randomSparseMatrix_cell_le M hR hqq hqR N hTscale p
  refine (Finset.sum_le_sum hcell).trans ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ T ∈ S, (volume T.openCarrier).toReal /
      (volume (openCubeSet Q)).toReal ≤ 1 := by
    rw [← Finset.sum_div, div_le_one hUpos]
    exact sum_volume_openCarrier_selfPartition_le Q
  have hnn : (0 : ℝ) ≤ qq ^ (N + 1) * vecNormSq p :=
    mul_nonneg (pow_nonneg hqq _) (vecNormSq_nonneg p)
  calc (∑ T ∈ S, (volume T.openCarrier).toReal /
          (volume (openCubeSet Q)).toReal) * (qq ^ (N + 1) * vecNormSq p)
      ≤ 1 * (qq ^ (N + 1) * vecNormSq p) := mul_le_mul_of_nonneg_right hsum hnn
    _ = qq ^ (N + 1) * vecNormSq p := one_mul _

/-! ## The scalar readout -/

theorem vecDot_matVecMul_single (A : Mat d) (i : Fin d) :
    vecDot (Pi.single i (1 : ℝ)) (matVecMul A (Pi.single i (1 : ℝ))) = A i i := by
  simp [vecDot, matVecMul, Pi.single_apply, Finset.sum_ite_eq']

theorem vecNormSq_single (i : Fin d) : vecNormSq (Pi.single i (1 : ℝ)) = 1 := by
  simp [vecNormSq, vecDot, Pi.single_apply, Finset.sum_ite_eq']

/-- **The scalar readout is an expected quadratic form.** -/
theorem abarScalarReadout_eq_integral_vecDot (M : GMCModel d) (m n : ℕ)
    (i : Fin d) :
    abarScalarReadout M m n =
      ∫ omega, vecDot (Pi.single i (1 : ℝ))
        (matVecMul (randomAMatrix M m
          (Ch02.cubeDomain (originCube d (n : ℤ))) omega) (Pi.single i (1 : ℝ)))
        ∂M.P.toMeasure := by
  have habar := abar_eq_abarScalarReadout_smul_one M m n
  have hentry : abar M m (Ch02.cubeDomain (originCube d (n : ℤ))) i i =
      abarScalarReadout M m n := by
    rw [habar]
    simp
  rw [← hentry, abar, Homogenization.integral_matrix_apply
    (integrable_randomAMatrix M m (Ch02.cubeDomain (originCube d (n : ℤ)))) i i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
  exact (vecDot_matVecMul_single (randomAMatrix M m
    (Ch02.cubeDomain (originCube d (n : ℤ))) omega) i).symm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
