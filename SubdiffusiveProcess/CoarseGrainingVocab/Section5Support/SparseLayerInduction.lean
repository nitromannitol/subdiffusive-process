module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OuterWeightTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerSigma
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.PartitionInterchange
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerInductionBase
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.MeanOneFubini

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Homogenization.Book Kuhn MeasureTheory ProbabilityTheory Set
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## Quadratic homogeneity -/

theorem vecDot_matVecMul_smul (A : Mat d) (t : ℝ) (p : Vec d) :
    vecDot (t • p) (matVecMul A (t • p)) = t ^ 2 * vecDot p (matVecMul A p) := by
  rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
  ring

/-- A `2`-homogeneous function bounded on the unit sphere is bounded by that
constant times `|p|^2`. -/
theorem le_mul_vecNormSq_of_forall_unit {f : Vec d → ℝ} {kappa : ℝ}
    (hhom : ∀ (t : ℝ) (p : Vec d), f (t • p) = t ^ 2 * f p)
    (hunit : ∀ p ∈ vecUnitSphere d, f p ≤ kappa) (p : Vec d) :
    f p ≤ kappa * vecNormSq p := by
  by_cases hp : p = 0
  · subst hp
    have h0 : f 0 = 0 := by simpa using hhom 0 0
    have hz : vecNormSq (0 : Vec d) = 0 := vecNormSq_eq_zero_iff.mpr rfl
    rw [h0, hz, mul_zero]
  · have hpos : 0 < vecNormSq p :=
      lt_of_le_of_ne (vecNormSq_nonneg p) fun h => hp (vecNormSq_eq_zero h.symm)
    set s : ℝ := Real.sqrt (vecNormSq p) with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 hpos
    have hs2 : s ^ 2 = vecNormSq p := Real.sq_sqrt (vecNormSq_nonneg p)
    have hu : (s⁻¹ • p) ∈ vecUnitSphere d := by
      show vecNormSq (s⁻¹ • p) = 1
      rw [vecNormSq_smul, ← hs2]
      field_simp
    have hkey : f p = s ^ 2 * f (s⁻¹ • p) := by
      have h := hhom s (s⁻¹ • p)
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hs0), one_smul] at h
      exact h
    rw [hkey, ← hs2, mul_comm kappa (s ^ 2)]
    exact mul_le_mul_of_nonneg_left (hunit _ hu) (by positivity)

/-! ## Mean-one domination for the sparse coefficient -/

theorem integrable_setIntegral_sparseLayerCoefficient (M : GMCModel d) {R : ℕ}
    (hR : 0 < R) (N : ℕ) {U : Set (Vec d)} (hU : MeasurableSet U)
    (hUb : Bornology.IsBounded U) :
    Integrable (fun omega : PotentialSample d =>
      ∫ x in U, sparseLayerCoefficient M R N omega x) M.P.toMeasure := by
  have h := integrable_setIntegral_layerCoefficient M (sparseLayerIndices R N) hU hUb
  refine h.congr (Filter.Eventually.of_forall fun omega => ?_)
  refine setIntegral_congr_fun hU fun x _ => ?_
  exact (sparseLayerCoefficient_eq_layerCoefficient M hR N omega x).symm

theorem integral_setIntegral_sparseLayerCoefficient (M : GMCModel d) {R : ℕ}
    (hR : 0 < R) (N : ℕ) {U : Set (Vec d)} (hU : MeasurableSet U)
    (hUb : Bornology.IsBounded U) :
    ∫ omega, (∫ x in U, sparseLayerCoefficient M R N omega x) ∂M.P.toMeasure =
      (volume U).toReal := by
  rw [← integral_setIntegral_layerCoefficient M (sparseLayerIndices R N) hU hUb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
  refine setIntegral_congr_fun hU fun x _ => ?_
  exact sparseLayerCoefficient_eq_layerCoefficient M hR N omega x

theorem measurable_vecDot_randomSparseMatrix (M : GMCModel d) {R : ℕ} (hR : 0 < R)
    (N : ℕ) (T : KuhnCell d) (q : Vec d) :
    Measurable fun omega : PotentialSample d =>
      vecDot q (matVecMul (randomSparseMatrix M R N (kuhnCellDomain T) omega) q) :=
  (measurable_vecDot_randomSparseMatrix_sparseLayerSigma M hR N T q).mono
    (potentialIndexSigma_le_borel _) le_rfl

theorem vecDot_randomSparseMatrix_nonneg (M : GMCModel d) (R N : ℕ)
    (U : Ch02.Domain d) (omega : PotentialSample d) (q : Vec d) :
    0 ≤ vecDot q (matVecMul (randomSparseMatrix M R N U omega) q) := by
  rw [vecDot_randomSparseMatrix_eq]
  refine mul_nonneg (by positivity) ?_
  exact dirichletInfOn_nonneg U.isOpen.measurableSet
    fun x => (sparseLayerCoefficient_pos M R N omega x).le

theorem vecDot_randomSparseMatrix_le_affine (M : GMCModel d) (R N : ℕ)
    (T : KuhnCell d) (omega : PotentialSample d) (q : Vec d) :
    vecDot q (matVecMul (randomSparseMatrix M R N (kuhnCellDomain T) omega) q) ≤
      (volume T.openCarrier).toReal⁻¹ * vecNormSq q *
        ∫ x in T.openCarrier, sparseLayerCoefficient M R N omega x := by
  rw [vecDot_randomSparseMatrix_eq, kuhnCellDomain_coe]
  have haff := dirichletInfOn_le_affine (B := sparseLayerCoefficient M R N omega)
    (U := T.openCarrier) (p := q) (isOpen_openCarrier T).measurableSet
    fun x => (sparseLayerCoefficient_pos M R N omega x).le
  have hconst : ∫ x in T.openCarrier,
      sparseLayerCoefficient M R N omega x * vecNormSq q =
      (∫ x in T.openCarrier, sparseLayerCoefficient M R N omega x) * vecNormSq q :=
    integral_mul_const _ _
  rw [hconst] at haff
  have hmul := mul_le_mul_of_nonneg_left haff
    (show (0 : ℝ) ≤ (volume T.openCarrier).toReal⁻¹ by positivity)
  refine hmul.trans (le_of_eq ?_)
  ring

/-- The inner quadratic form is integrable: the affine competitor and the
mean-one normalization of the sparse coefficient. -/
theorem integrable_vecDot_randomSparseMatrix (M : GMCModel d) {R : ℕ} (hR : 0 < R)
    (N : ℕ) (T : KuhnCell d) (q : Vec d) :
    Integrable (fun omega : PotentialSample d =>
      vecDot q (matVecMul (randomSparseMatrix M R N (kuhnCellDomain T) omega) q))
      M.P.toMeasure := by
  have hmeas := measurable_vecDot_randomSparseMatrix M hR N T q
  have hdom : Integrable (fun omega : PotentialSample d =>
      (volume T.openCarrier).toReal⁻¹ * vecNormSq q *
        ∫ x in T.openCarrier, sparseLayerCoefficient M R N omega x) M.P.toMeasure :=
    (integrable_setIntegral_sparseLayerCoefficient M hR N
      (isOpen_openCarrier T).measurableSet (isBounded_openCarrier T)).const_mul _
  refine hdom.mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (vecDot_randomSparseMatrix_nonneg M R N (kuhnCellDomain T) omega q)]
  exact vecDot_randomSparseMatrix_le_affine M R N T omega q

/-! ## The deterministic display at the transported mesh -/



theorem vecDot_randomSparseMatrix_succ_le (M : GMCModel d) (R N k : ℕ)
    (c : Fin d → ℤ) (pi : Equiv.Perm (Fin d)) (p : Vec d)
    (omega : PotentialSample d)
    (comp : KuhnCompetitor (dilatedCell k c pi).openCarrier
      (dilatedSubMesh k R c pi)) :
    vecDot p (matVecMul (randomSparseMatrix M R (N + 1)
        (kuhnCellDomain (dilatedCell k c pi)) omega) p) ≤
      ∑ T ∈ dilatedSubMesh k R c pi,
        (volume T.openCarrier).toReal /
            (volume (dilatedCell k c pi).openCarrier).toReal *
          (cellSup (shellFactor M ((N + 1) * R) omega) T *
            vecDot (p + comp.slope T)
              (matVecMul (randomSparseMatrix M R N (kuhnCellDomain T) omega)
                (p + comp.slope T))) := by
  set B : Vec d → ℝ := shellFactor M ((N + 1) * R) omega with hBdef
  set A : Vec d → ℝ := sparseLayerCoefficient M R N omega with hAdef
  have hA : Continuous A := continuous_sparseLayerCoefficient M R N omega
  have hA0 : ∀ x, 0 ≤ A x := fun x => (sparseLayerCoefficient_pos M R N omega x).le
  have hB : Continuous B := continuous_shellFactor M ((N + 1) * R) omega
  have hB0 : ∀ x, 0 ≤ B x := fun _ => (Real.exp_pos _).le
  have hprod : Continuous fun x => B x * A x := hB.mul hA
  have hprodpos : ∀ x, 0 < B x * A x := fun x =>
    mul_pos (Real.exp_pos _) (sparseLayerCoefficient_pos M R N omega x)
  set hBA : ScalarCoeffOnData (kuhnCellDomain (dilatedCell k c pi))
      (fun x => B x * A x) :=
    scalarCoeffOnDataOfContinuousPos hprod hprodpos
      (kuhnCellDomain (dilatedCell k c pi)) with hBAdef
  set hAV : ∀ T : KuhnCell d, ScalarCoeffOnData (kuhnCellDomain T) A :=
    fun T => sparseLayerCoeffOnData M R N omega (kuhnCellDomain T) with hAVdef
  have hmain := vecDot_aMatrix_le_sum_cellSup_vecDot_aMatrix
    (A := A) (B := B) (S := dilatedSubMesh k R c pi) (s := (k : ℤ) - (R : ℤ))
    (p := p) (U := kuhnCellDomain (dilatedCell k c pi))
    (V := fun T => kuhnCellDomain T)
    hA hA0 hB hB0 (fun T hT => scale_of_mem_dilatedSubMesh hT) (fun _ _ => rfl)
    (fun T hT => openCarrier_subset_of_mem_dilatedSubMesh hT)
    (openCarrier_dilatedCell_subset_iUnion k R c pi) comp hBA hAV
  have hlhs : vecDot p (matVecMul (randomSparseMatrix M R (N + 1)
        (kuhnCellDomain (dilatedCell k c pi)) omega) p) =
      vecDot p (matVecMul (aMatrix (kuhnCellDomain (dilatedCell k c pi))
        hBA.toCoeffOn) p) := by
    rw [randomSparseMatrix,
      vecDot_aMatrix_eq_dirichletInfOn (sparseLayerCoeffOnData M R (N + 1) omega
        (kuhnCellDomain (dilatedCell k c pi)))
        (fun x => (sparseLayerCoefficient_pos M R (N + 1) omega x).le) p,
      vecDot_aMatrix_eq_dirichletInfOn hBA (fun x => (hprodpos x).le) p,
      sparseLayerCoefficient_succ M R N omega]
  rw [hlhs]
  exact hmain

/-! ## Measurability and integrability of the outer weights -/

theorem measurable_cellSup_shellFactor' (M : GMCModel d) (k : ℕ) (T : KuhnCell d) :
    Measurable fun omega : PotentialSample d =>
      cellSup (shellFactor M k omega) T :=
  measurable_cellSup T (fun omega => continuous_shellFactor M k omega)
    fun y => ((measurable_shell_eval k y).sub measurable_const).exp

/-- The outer cell weight is measurable for the sigma-algebra of its own
layer. -/
theorem measurable_cellSup_shellFactor_singleton (M : GMCModel d) (k : ℕ)
    (T : KuhnCell d) :
    Measurable[potentialIndexSigma (d := d) ({k} : Set ℕ)]
      fun omega : PotentialSample d => cellSup (shellFactor M k omega) T := by
  have h := measurable_cellSup_layerCoefficient_potentialIndexSigma M {k} T
  rw [Finset.coe_singleton] at h
  have hfun : (fun omega : PotentialSample d =>
      cellSup (layerCoefficient M {k} omega) T) =
      fun omega : PotentialSample d => cellSup (shellFactor M k omega) T := by
    funext omega
    congr 1
    funext x
    simp [layerCoefficient]
  rwa [hfun] at h

theorem integrable_cellSup_shellFactor_mem_dilatedSubMesh (M : GMCModel d)
    (R k : ℕ) (c : Fin d → ℤ) (pi : Equiv.Perm (Fin d)) {T : KuhnCell d}
    (hT : T ∈ dilatedSubMesh k R c pi) :
    Integrable (fun omega : PotentialSample d =>
      cellSup (shellFactor M k omega) T) M.P.toMeasure := by
  obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hT
  exact integrable_cellSup_shellFactor_dilateKuhnCell M R k c pi hV

/-- The discrete minimum of the outer layer on the transported mesh is
integrable. -/
theorem integrable_kuhnDirichletInf_shellFactor_dilated (M : GMCModel d)
    (R k : ℕ) (c : Fin d → ℤ) (pi : Equiv.Perm (Fin d)) (p : Vec d) :
    Integrable (fun omega : PotentialSample d =>
      kuhnDirichletInf (shellFactor M k omega) (dilatedSubMesh k R c pi)
        (dilatedCell k c pi).openCarrier p) M.P.toMeasure := by
  have hmeas : Measurable fun omega : PotentialSample d =>
      kuhnDirichletInf (shellFactor M k omega) (dilatedSubMesh k R c pi)
        (dilatedCell k c pi).openCarrier p :=
    measurable_kuhnDirichletInf (fun omega => continuous_shellFactor M k omega)
      (fun omega x => (shellFactor_pos M k omega x).le)
      fun T _ => measurable_cellSup_shellFactor' M k T
  have hdom : Integrable (fun omega : PotentialSample d =>
      ∑ T ∈ dilatedSubMesh k R c pi,
        volume.real ((dilatedCell k c pi).openCarrier ∩ T.openCarrier) *
          (cellSup (shellFactor M k omega) T * vecNormSq p)) M.P.toMeasure := by
    refine integrable_finset_sum _ fun T hT => ?_
    exact ((integrable_cellSup_shellFactor_mem_dilatedSubMesh M R k c pi
      hT).mul_const _).const_mul _
  refine hdom.mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (kuhnDirichletInf_nonneg
    (continuous_shellFactor M k omega)
    (fun x => (shellFactor_pos M k omega x).le) p)]
  exact kuhnDirichletInf_le_affine (continuous_shellFactor M k omega)
    (fun x => (shellFactor_pos M k omega x).le) p

/-! ## The inductive statement -/

/-- **`e.strict.decay.sparse.induction`** at one generation: the expected
quadratic form of the sparse coefficient on every triadic simplex of size
`3^{NR}`. -/
def SparseLayerBound (M : GMCModel d) (R N : ℕ) (kappa : ℝ) : Prop :=
  ∀ (c : Fin d → ℤ) (pi : Equiv.Perm (Fin d)) (q : Vec d),
    ∫ omega, vecDot q (matVecMul (randomSparseMatrix M R N
        (kuhnCellDomain (dilatedCell (N * R) c pi)) omega) q) ∂M.P.toMeasure ≤
      kappa * vecNormSq q

/-- Every triadic cell of size `3^k` is a `dilatedCell`. -/
theorem eq_dilatedCell {T : KuhnCell d} {k : ℕ} (hT : T.supportCube.scale = (k : ℤ)) :
    T = dilatedCell k T.supportCube.index T.order := by
  cases T with
  | mk Q sigma =>
      cases Q with
      | mk sc idx =>
          simp only at hT
          subst hT
          rfl

/-! ## The inductive step -/



theorem sparseLayerBound_succ (M : GMCModel d) {R : ℕ} (hR : 0 < R) (N : ℕ)
    {kap qq : ℝ} (hkap : 0 ≤ kap)
    (hIH : SparseLayerBound M R N kap)
    (hqR : ∀ pi : Equiv.Perm (Fin d),
      qRCell M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) ≤ qq) :
    SparseLayerBound M R (N + 1) (kap * qq) := by
  intro c pi p
  set k : ℕ := (N + 1) * R with hk
  set U : KuhnCell d := dilatedCell k c pi with hU
  set S : Finset (KuhnCell d) := dilatedSubMesh k R c pi with hS
  have hvolU : 0 < (volume U.openCarrier).toReal :=
    volume_toReal_pos (kuhnCellDomain U)
  have hUmeas : MeasurableSet U.openCarrier := (isOpen_openCarrier U).measurableSet
  -- the outer block and the inner block are disjoint
  have hdisj : Disjoint ((sparseLayerIndices R N : Finset ℕ) : Set ℕ)
      ({k} : Set ℕ) := disjoint_sparseLayerIndices_succ hR N
  refine le_mul_vecNormSq_of_forall_unit
    (f := fun q => ∫ omega, vecDot q (matVecMul (randomSparseMatrix M R (N + 1)
      (kuhnCellDomain U) omega) q) ∂M.P.toMeasure)
    (kappa := kap * qq) ?_ ?_ p
  · intro t r
    calc ∫ omega, vecDot (t • r) (matVecMul (randomSparseMatrix M R (N + 1)
            (kuhnCellDomain U) omega) (t • r)) ∂M.P.toMeasure
        = ∫ omega, t ^ 2 * vecDot r (matVecMul (randomSparseMatrix M R (N + 1)
            (kuhnCellDomain U) omega) r) ∂M.P.toMeasure := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
          exact vecDot_matVecMul_smul _ t r
      _ = t ^ 2 * ∫ omega, vecDot r (matVecMul (randomSparseMatrix M R (N + 1)
            (kuhnCellDomain U) omega) r) ∂M.P.toMeasure := integral_const_mul _ _
  intro u hu
  have hu1 : vecNormSq u = 1 := hu
  -- it suffices to bound by `kap * qq` up to an arbitrary positive error
  refine le_of_forall_pos_le_add fun err herr => ?_
  set eps : ℝ := err * (volume U.openCarrier).toReal / (kap + 1) with heps'
  have hkap1 : (0 : ℝ) < kap + 1 := by linarith
  have heps : 0 < eps := by
    rw [heps']
    positivity
  -- the measurable, countably valued selection, on the outer layer's block
  obtain ⟨D, n, hD, hn, hopt⟩ :=
    @exists_measurable_eps_optimal_kuhnSlopes d (PotentialSample d)
      (potentialIndexSigma ({k} : Set ℕ))
      (fun omega => shellFactor M k omega) S U.openCarrier u
      (fun omega => continuous_shellFactor M k omega)
      (fun omega x => (shellFactor_pos M k omega x).le)
      (fun T _ => measurable_cellSup_shellFactor_singleton M k T) eps heps
  have hn' : Measurable n := hn.mono (potentialIndexSigma_le_borel _) le_rfl
  choose comp hcomp using hD
  -- the two integrands
  set X : PotentialSample d → ℝ := fun omega =>
    vecDot u (matVecMul (randomSparseMatrix M R (N + 1)
      (kuhnCellDomain U) omega) u) with hXdef
  set H : PotentialSample d → ℝ := fun omega =>
    (volume U.openCarrier).toReal⁻¹ *
      (kuhnDirichletInf (shellFactor M k omega) S U.openCarrier u + eps) with hHdef
  have hXint : Integrable X M.P.toMeasure :=
    integrable_vecDot_randomSparseMatrix M hR (N + 1) U u
  have hHint : Integrable H M.P.toMeasure :=
    Integrable.const_mul (Integrable.add
      (integrable_kuhnDirichletInf_shellFactor_dilated M R k c pi u)
      (integrable_const eps)) _
  have hkapHint : Integrable (fun omega => kap * H omega) M.P.toMeasure :=
    hHint.const_mul _
  -- integrability of the pieces
  have hcellint : ∀ T ∈ S, Integrable (fun omega : PotentialSample d =>
      cellSup (shellFactor M k omega) T) M.P.toMeasure := fun T hT =>
    integrable_cellSup_shellFactor_mem_dilatedSubMesh M R k c pi hT
  have hcellmeas : ∀ T : KuhnCell d, Measurable fun omega : PotentialSample d =>
      cellSup (shellFactor M k omega) T := fun T =>
    measurable_cellSup_shellFactor' M k T
  -- the scale of a cell of the mesh
  have hTscale : ∀ T ∈ S, T.supportCube.scale = ((N * R : ℕ) : ℤ) := by
    intro T hT
    rw [scale_of_mem_dilatedSubMesh hT, hk]
    push_cast
    ring
  -- the induction hypothesis, read at a cell of the mesh
  have hIHcell : ∀ T ∈ S, ∀ q : Vec d,
      ∫ omega, vecDot q (matVecMul (randomSparseMatrix M R N
        (kuhnCellDomain T) omega) q) ∂M.P.toMeasure ≤ kap * vecNormSq q := by
    intro T hT q
    have hTeq : T = dilatedCell (N * R) T.supportCube.index T.order :=
      eq_dilatedCell (hTscale T hT)
    rw [hTeq]
    exact hIH _ _ q
  -- the fibrewise comparison
  have hfiber : ∀ m : ℕ,
      ∫ omega in {omega | n omega = m}, X omega ∂M.P.toMeasure ≤
        ∫ omega in {omega | n omega = m}, kap * H omega ∂M.P.toMeasure := by
    intro m
    have hFmeas : MeasurableSet {omega : PotentialSample d | n omega = m} :=
      measurableSet_index_fiber hn' m
    -- the deterministic display at the frozen slopes
    have hstep1 : ∀ omega : PotentialSample d, X omega ≤
        ∑ T ∈ S, (volume T.openCarrier).toReal /
            (volume U.openCarrier).toReal *
          (cellSup (shellFactor M k omega) T *
            vecDot (u + D m T) (matVecMul (randomSparseMatrix M R N
              (kuhnCellDomain T) omega) (u + D m T))) := by
      intro omega
      have h := vecDot_randomSparseMatrix_succ_le M R N k c pi u omega (comp m)
      rw [hcomp m] at h
      exact h
    have hterm : ∀ T ∈ S, Integrable (fun omega : PotentialSample d =>
        (volume T.openCarrier).toReal / (volume U.openCarrier).toReal *
          (cellSup (shellFactor M k omega) T *
            vecDot (u + D m T) (matVecMul (randomSparseMatrix M R N
              (kuhnCellDomain T) omega) (u + D m T)))) M.P.toMeasure := by
      intro T hT
      refine Integrable.const_mul ?_ _
      have hind : IndepFun
          (fun omega : PotentialSample d => cellSup (shellFactor M k omega) T)
          (fun omega : PotentialSample d => vecDot (u + D m T)
            (matVecMul (randomSparseMatrix M R N (kuhnCellDomain T) omega)
              (u + D m T))) M.P.toMeasure :=
        (indepFun_of_potentialIndexSigma_disjoint M hdisj
          (measurable_vecDot_randomSparseMatrix_sparseLayerSigma M hR N T (u + D m T))
          (measurable_cellSup_shellFactor_singleton M k T)).symm
      exact hind.integrable_mul (hcellint T hT)
        (integrable_vecDot_randomSparseMatrix M hR N T (u + D m T))
    -- integrate the display over the fiber
    have hstep2 : ∫ omega in {omega | n omega = m}, X omega ∂M.P.toMeasure ≤
        ∑ T ∈ S, (volume T.openCarrier).toReal /
            (volume U.openCarrier).toReal *
          ((∫ omega in {omega | n omega = m},
              cellSup (shellFactor M k omega) T ∂M.P.toMeasure) *
            ∫ omega, vecDot (u + D m T) (matVecMul (randomSparseMatrix M R N
              (kuhnCellDomain T) omega) (u + D m T)) ∂M.P.toMeasure) := by
      have hle := setIntegral_mono_on hXint.integrableOn
        (integrable_finset_sum S hterm).integrableOn hFmeas
        (fun omega _ => hstep1 omega)
      refine hle.trans (le_of_eq ?_)
      rw [integral_finset_sum S fun T hT => (hterm T hT).integrableOn]
      refine Finset.sum_congr rfl fun T hT => ?_
      rw [integral_const_mul]
      congr 1
      rw [setIntegral_mul_eq_integral_indicator_mul hFmeas]
      have hind : IndepFun
          (Set.indicator {omega : PotentialSample d | n omega = m}
            (fun omega => cellSup (shellFactor M k omega) T))
          (fun omega : PotentialSample d => vecDot (u + D m T)
            (matVecMul (randomSparseMatrix M R N (kuhnCellDomain T) omega)
              (u + D m T))) M.P.toMeasure :=
        (indepFun_of_potentialIndexSigma_disjoint M hdisj
          (measurable_vecDot_randomSparseMatrix_sparseLayerSigma M hR N T (u + D m T))
          (measurable_indicator_fiber_mul hn
            (measurable_cellSup_shellFactor_singleton M k T) m)).symm
      rw [hind.integral_fun_mul_eq_mul_integral
        ((((hcellmeas T).indicator hFmeas)).aestronglyMeasurable)
        (measurable_vecDot_randomSparseMatrix M hR N T (u + D m T)).aestronglyMeasurable,
        integral_indicator hFmeas]
    -- apply the induction hypothesis termwise
    have hstep3 : ∑ T ∈ S, (volume T.openCarrier).toReal /
            (volume U.openCarrier).toReal *
          ((∫ omega in {omega | n omega = m},
              cellSup (shellFactor M k omega) T ∂M.P.toMeasure) *
            ∫ omega, vecDot (u + D m T) (matVecMul (randomSparseMatrix M R N
              (kuhnCellDomain T) omega) (u + D m T)) ∂M.P.toMeasure) ≤
        kap * ∫ omega in {omega | n omega = m},
          (volume U.openCarrier).toReal⁻¹ *
            kuhnDiscreteEnergy (shellFactor M k omega) S U.openCarrier u (D m)
            ∂M.P.toMeasure := by
      have hweight : ∀ T ∈ S, 0 ≤ ∫ omega in {omega | n omega = m},
          cellSup (shellFactor M k omega) T ∂M.P.toMeasure := by
        intro T hT
        refine setIntegral_nonneg hFmeas fun omega _ => ?_
        exact le_trans (shellFactor_pos M k omega (T.vertex 0)).le
          (le_cellSup T (continuous_shellFactor M k omega).continuousOn
            (T.vertex_mem_closedCarrier 0))
      have hbound : ∀ T ∈ S,
          (volume T.openCarrier).toReal / (volume U.openCarrier).toReal *
            ((∫ omega in {omega | n omega = m},
                cellSup (shellFactor M k omega) T ∂M.P.toMeasure) *
              ∫ omega, vecDot (u + D m T) (matVecMul (randomSparseMatrix M R N
                (kuhnCellDomain T) omega) (u + D m T)) ∂M.P.toMeasure) ≤
            kap * ∫ omega in {omega | n omega = m},
              (volume U.openCarrier).toReal⁻¹ *
                (volume.real (U.openCarrier ∩ T.openCarrier) *
                  (cellSup (shellFactor M k omega) T *
                    vecNormSq (u + D m T))) ∂M.P.toMeasure := by
        intro T hT
        have hsetT : U.openCarrier ∩ T.openCarrier = T.openCarrier :=
          Set.inter_eq_self_of_subset_right
            (openCarrier_subset_of_mem_dilatedSubMesh hT)
        have hinner := hIHcell T hT (u + D m T)
        have hmul := mul_le_mul_of_nonneg_left hinner (hweight T hT)
        have hmul2 := mul_le_mul_of_nonneg_left hmul
          (show (0 : ℝ) ≤ (volume T.openCarrier).toReal /
            (volume U.openCarrier).toReal by positivity)
        refine hmul2.trans (le_of_eq ?_)
        rw [hsetT]
        have hC : ∀ omega : PotentialSample d,
            (volume U.openCarrier).toReal⁻¹ *
              (volume.real T.openCarrier *
                (cellSup (shellFactor M k omega) T * vecNormSq (u + D m T))) =
              ((volume U.openCarrier).toReal⁻¹ *
                (volume.real T.openCarrier * vecNormSq (u + D m T))) *
                cellSup (shellFactor M k omega) T := fun omega => by ring
        simp only [hC]
        rw [integral_const_mul]
        have hvne : (volume U.openCarrier).toReal ≠ 0 := ne_of_gt hvolU
        have hreal : volume.real T.openCarrier = (volume T.openCarrier).toReal := rfl
        rw [hreal]
        field_simp
      have hsum : ∑ T ∈ S, ∫ omega in {omega | n omega = m},
          (volume U.openCarrier).toReal⁻¹ *
            (volume.real (U.openCarrier ∩ T.openCarrier) *
              (cellSup (shellFactor M k omega) T * vecNormSq (u + D m T)))
            ∂M.P.toMeasure =
          ∫ omega in {omega | n omega = m},
            (volume U.openCarrier).toReal⁻¹ *
              kuhnDiscreteEnergy (shellFactor M k omega) S U.openCarrier u (D m)
              ∂M.P.toMeasure := by
        rw [← integral_finset_sum S fun T hT =>
          ((((hcellint T hT).mul_const _).const_mul _).const_mul _).integrableOn]
        refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
        simp only [kuhnDiscreteEnergy, Finset.mul_sum]
      refine (Finset.sum_le_sum hbound).trans (le_of_eq ?_)
      rw [← Finset.mul_sum, hsum]
    -- the selection is `eps`-optimal on its fiber
    have hstep4 : kap * ∫ omega in {omega | n omega = m},
          (volume U.openCarrier).toReal⁻¹ *
            kuhnDiscreteEnergy (shellFactor M k omega) S U.openCarrier u (D m)
            ∂M.P.toMeasure ≤
        ∫ omega in {omega | n omega = m}, kap * H omega ∂M.P.toMeasure := by
      conv_rhs => rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ hkap
      refine setIntegral_mono_on ?_ hHint.integrableOn hFmeas fun omega homega => ?_
      · refine Integrable.integrableOn ?_
        refine Integrable.const_mul ?_ _
        refine integrable_finset_sum S fun T hT => ?_
        exact ((hcellint T hT).mul_const _).const_mul _
      · have hval : D (n omega) = D m := by
          rw [show n omega = m from homega]
        have := hopt omega
        rw [hval] at this
        refine mul_le_mul_of_nonneg_left (le_of_lt this) (by positivity)
    exact hstep2.trans (hstep3.trans hstep4)
  -- assemble
  have hmain : ∫ omega, X omega ∂M.P.toMeasure ≤
      ∫ omega, kap * H omega ∂M.P.toMeasure :=
    integral_le_of_setIntegral_fiber_le hn' hXint hkapHint hfiber
  have hHval : ∫ omega, H omega ∂M.P.toMeasure ≤
      qRSlope M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) u +
        (volume U.openCarrier).toReal⁻¹ * eps := by
    rw [hHdef]
    rw [integral_const_mul, integral_add
      (integrable_kuhnDirichletInf_shellFactor_dilated M R k c pi u)
      (integrable_const eps), integral_const, mul_add]
    have hq := integral_normalized_kuhnDirichletInf_shellFactor_le M R k c pi u
    rw [integral_const_mul] at hq
    have hmeasure : (M.P.toMeasure).real Set.univ = 1 := by simp
    rw [smul_eq_mul, hmeasure, one_mul]
    linarith [hq]
  have hqfinal : qRSlope M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) u ≤ qq := by
    refine le_trans (qRSlope_le_qRCell M ?_ _ hu) (hqR pi)
    intro V hV
    exact closedCarrier_subset_of_mem_unitMesh (by omega) hV
  have herrbound : kap * ((volume U.openCarrier).toReal⁻¹ * eps) ≤ err := by
    rw [heps']
    have hvne : (volume U.openCarrier).toReal ≠ 0 := ne_of_gt hvolU
    rw [show (volume U.openCarrier).toReal⁻¹ *
        (err * (volume U.openCarrier).toReal / (kap + 1)) = err / (kap + 1) by
      field_simp]
    rw [mul_div_assoc']
    rw [div_le_iff₀ hkap1]
    nlinarith [herr.le, hkap]
  calc ∫ omega, X omega ∂M.P.toMeasure
      ≤ ∫ omega, kap * H omega ∂M.P.toMeasure := hmain
    _ = kap * ∫ omega, H omega ∂M.P.toMeasure := integral_const_mul _ _
    _ ≤ kap * (qq + (volume U.openCarrier).toReal⁻¹ * eps) := by
        refine mul_le_mul_of_nonneg_left ?_ hkap
        linarith [hHval, hqfinal]
    _ = kap * qq + kap * ((volume U.openCarrier).toReal⁻¹ * eps) := by ring
    _ ≤ kap * qq + err := by linarith [herrbound]

/-! ## The base case and the induction -/

theorem measurable_dirichletInfOn_shellWeight (M : GMCModel d) (T : KuhnCell d)
    (p : Vec d) :
    Measurable fun g : PotentialField d =>
      dirichletInfOn (shellWeight M g) T.openCarrier p := by
  obtain ⟨n0, rfl⟩ : ∃ n0 : ℕ, d = n0 + 1 :=
    ⟨d - 1, by have := M.shellPrefix.dimension; omega⟩
  have hcont : ∀ g : PotentialField (n0 + 1), Continuous (shellWeight M g) :=
    fun g => Real.continuous_exp.comp
      ((g.contDiff_one.continuous).sub continuous_const)
  exact measurable_dirichletInfOn (isOpenBoundedConvexDomain_openCarrier T)
    T.openCarrier_subset_openCubeSet hcont (fun g x => (Real.exp_pos _).le) p
    fun V => measurable_cellSup V hcont
      fun y => ((PotentialField.measurable_eval y).sub measurable_const).exp

/-- **The base case `N = 0` of `e.strict.decay.sparse.induction`**, at every
triadic simplex of unit size. -/
theorem sparseLayerBound_zero (M : GMCModel d) {R : ℕ} {qq : ℝ}
    (hqR : ∀ pi : Equiv.Perm (Fin d),
      qRCell M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) ≤ qq) :
    SparseLayerBound M R 0 qq := by
  intro c pi q
  simp only [Nat.zero_mul]
  set T : KuhnCell d := dilatedCell 0 c pi with hT
  have hscale : T.supportCube.scale = ((0 : ℕ) : ℤ) := rfl
  have horder : T.order = pi := rfl
  have hpt : ∀ omega : PotentialSample d, ∀ r : Vec d,
      vecDot r (matVecMul (randomSparseMatrix M R 0 (kuhnCellDomain T) omega) r) =
        (volume T.openCarrier).toReal⁻¹ *
          dirichletInfOn (shellFactor M 0 omega) T.openCarrier r := by
    intro omega r
    rw [vecDot_randomSparseMatrix_eq, kuhnCellDomain_coe,
      sparseLayerCoefficient_zero]
  have hkey : ∀ r : Vec d,
      ∫ omega, vecDot r (matVecMul (randomSparseMatrix M R 0
          (kuhnCellDomain T) omega) r) ∂M.P.toMeasure =
        qStarSlope M (originKuhnCell d pi 0) r := by
    intro r
    have heq := integral_normalized_dirichletInfOn_shellFactor_cell_eq M T 0 hscale r
      (measurable_dirichletInfOn_shellWeight M (originKuhnCell d T.order ((0 : ℕ) : ℤ)) r)
      (measurable_dirichletInfOn_shellWeight M (originKuhnCell d T.order 0) r)
    calc ∫ omega, vecDot r (matVecMul (randomSparseMatrix M R 0
            (kuhnCellDomain T) omega) r) ∂M.P.toMeasure
        = ∫ omega, (volume T.openCarrier).toReal⁻¹ *
            dirichletInfOn (shellFactor M 0 omega) T.openCarrier r
            ∂M.P.toMeasure := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
          exact hpt omega r
      _ = ∫ omega, (volume (originKuhnCell d T.order 0).openCarrier).toReal⁻¹ *
            dirichletInfOn (shellFactor M 0 omega)
              (originKuhnCell d T.order 0).openCarrier r ∂M.P.toMeasure := heq
      _ = qStarSlope M (originKuhnCell d pi 0) r := by
          rw [integral_const_mul, horder, qStarSlope_eq_inv_mul]
  refine le_mul_vecNormSq_of_forall_unit
    (f := fun r => ∫ omega, vecDot r (matVecMul (randomSparseMatrix M R 0
      (kuhnCellDomain T) omega) r) ∂M.P.toMeasure) (kappa := qq) ?_ ?_ q
  · intro t r
    calc ∫ omega, vecDot (t • r) (matVecMul (randomSparseMatrix M R 0
            (kuhnCellDomain T) omega) (t • r)) ∂M.P.toMeasure
        = ∫ omega, t ^ 2 * vecDot r (matVecMul (randomSparseMatrix M R 0
            (kuhnCellDomain T) omega) r) ∂M.P.toMeasure := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
          exact vecDot_matVecMul_smul _ t r
      _ = t ^ 2 * ∫ omega, vecDot r (matVecMul (randomSparseMatrix M R 0
            (kuhnCellDomain T) omega) r) ∂M.P.toMeasure := integral_const_mul _ _
  · intro r hr
    show (∫ omega, vecDot r (matVecMul (randomSparseMatrix M R 0
      (kuhnCellDomain T) omega) r) ∂M.P.toMeasure) ≤ qq
    rw [hkey r]
    refine le_trans (qStarSlope_le_qRSlope M rfl (show -(R : ℤ) ≤ 0 by omega) r) ?_
    refine le_trans (qRSlope_le_qRCell M ?_ _ hr) (hqR pi)
    intro V hV
    exact closedCarrier_subset_of_mem_unitMesh (by omega) hV



theorem sparseLayerBound_pow (M : GMCModel d) {R : ℕ} (hR : 0 < R) {qq : ℝ}
    (hqq : 0 ≤ qq)
    (hqR : ∀ pi : Equiv.Perm (Fin d),
      qRCell M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) ≤ qq) (N : ℕ) :
    SparseLayerBound M R N (qq ^ (N + 1)) := by
  induction N with
  | zero => simpa using sparseLayerBound_zero M hqR
  | succ N ih =>
      have h := sparseLayerBound_succ M hR N (pow_nonneg hqq (N + 1)) ih hqR
      have hpow : qq ^ (N + 1) * qq = qq ^ (N + 1 + 1) := (pow_succ qq (N + 1)).symm
      rwa [hpow] at h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
