module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.CellSupMoment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DiscreteSlopeModulus

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open MeasureTheory Homogenization Homogenization.Book Kuhn
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## The mesh of the unit cube -/

/-- The standard decomposition of the unit cube at scale `j`; the source's
`T_{R,pi}` is `unitMesh (-R)`. -/
def unitMesh (d : ℕ) (j : ℤ) : Finset (KuhnCell d) :=
  triadicSimplexPartition (originCube d 0) j

theorem closedCarrier_subset_of_mem_unitMesh {j : ℤ} (hj : j ≤ 0) {V : KuhnCell d}
    (hV : V ∈ unitMesh d j) :
    V.closedCarrier ⊆ Metric.closedBall (cubeCenter (originCube d 0))
      (cubeRadius (originCube d 0)) :=
  closedCarrier_subset_closedBall_of_mem_triadicSimplexPartition hj hV

theorem pairwiseDisjoint_unitMesh (d : ℕ) (j : ℤ) :
    (unitMesh d j : Set (KuhnCell d)).PairwiseDisjoint KuhnCell.openCarrier :=
  triadicSimplexPartition_openCarrier_pairwiseDisjoint _ _

/-! ## The mesh-uniform envelope of the cell weights -/

theorem cellSup_shellFactor_le_shellEnvelope (M : GMCModel d)
    (omega : PotentialSample d) {j : ℤ} (hj : j ≤ 0) {V : KuhnCell d}
    (hV : V ∈ unitMesh d j) :
    cellSup (shellFactor M 0 omega) V ≤ shellEnvelope M omega :=
  cellSup_shellFactor_le M omega (closedCarrier_subset_of_mem_unitMesh hj hV)

theorem volume_openCarrier_ne_top (T : KuhnCell d) : volume T.openCarrier ≠ ⊤ :=
  ne_of_lt (isBounded_openCarrier T).measure_lt_top



theorem kuhnWeightSum_shellFactor_le (M : GMCModel d) (omega : PotentialSample d)
    {j : ℤ} (hj : j ≤ 0) (T : KuhnCell d) :
    kuhnWeightSum (shellFactor M 0 omega) (unitMesh d j) T.openCarrier ≤
      shellEnvelope M omega * volume.real T.openCarrier :=
  kuhnWeightSum_le_mul (isOpen_openCarrier T).measurableSet
    (volume_openCarrier_ne_top T) (shellEnvelope_pos M omega).le
    (fun _ hV => cellSup_shellFactor_le_shellEnvelope M omega hj hV)
    (pairwiseDisjoint_unitMesh d j)

theorem integrable_kuhnWeightSum_shellFactor (M : GMCModel d) {j : ℤ} (hj : j ≤ 0)
    (T : KuhnCell d) :
    Integrable (fun omega : PotentialSample d =>
      kuhnWeightSum (shellFactor M 0 omega) (unitMesh d j) T.openCarrier)
      M.P.toMeasure := by
  refine integrable_finset_sum _ fun V hV => ?_
  exact (integrable_cellSup_shellFactor M
    (closedCarrier_subset_of_mem_unitMesh hj hV)).const_mul _

/-! ## Dominated convergence at a fixed slope -/

theorem kuhnDirichletInf_shellFactor_le_bound (M : GMCModel d)
    (omega : PotentialSample d) {j : ℤ} (hj : j ≤ 0) (T : KuhnCell d) (p : Vec d) :
    kuhnDirichletInf (shellFactor M 0 omega) (unitMesh d j) T.openCarrier p ≤
      vecNormSq p * (shellEnvelope M omega * volume.real T.openCarrier) := by
  refine le_trans (kuhnDirichletInf_le_weightSum (continuous_shellFactor M 0 omega)
    (fun x => (shellFactor_pos M 0 omega x).le) p) ?_
  exact mul_le_mul_of_nonneg_left (kuhnWeightSum_shellFactor_le M omega hj T)
    (vecNormSq_nonneg p)



theorem tendsto_integral_kuhnDirichletInf_shellFactor (M : GMCModel d)
    {T : KuhnCell d} (hT : T.supportCube = originCube d 0) (p : Vec d) :
    Filter.Tendsto
      (fun j : ℤ => ∫ omega, kuhnDirichletInf (shellFactor M 0 omega)
        (unitMesh d j) T.openCarrier p ∂M.P.toMeasure)
      Filter.atBot
      (nhds (∫ omega, dirichletInfOn (shellFactor M 0 omega) T.openCarrier p
        ∂M.P.toMeasure)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = n + 1 :=
    ⟨d - 1, by have := M.shellPrefix.dimension; omega⟩
  have hUQ : T.openCarrier ⊆ openCubeSet (originCube (n + 1) 0) := by
    rw [← hT]
    exact T.openCarrier_subset_openCubeSet
  refine tendsto_integral_filter_of_dominated_convergence
    (bound := fun omega : PotentialSample (n + 1) =>
      vecNormSq p * (shellEnvelope M omega * volume.real T.openCarrier)) ?_ ?_ ?_ ?_
  · filter_upwards with j
    exact (measurable_kuhnDirichletInf (fun omega => continuous_shellFactor M 0 omega)
      (fun omega x => (shellFactor_pos M 0 omega x).le)
      fun V _ => measurable_cellSup_shellFactor M V).aestronglyMeasurable
  · filter_upwards [Filter.eventually_le_atBot (0 : ℤ)] with j hj
    refine Filter.Eventually.of_forall fun omega => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (kuhnDirichletInf_nonneg
      (continuous_shellFactor M 0 omega)
      (fun x => (shellFactor_pos M 0 omega x).le) p)]
    exact kuhnDirichletInf_shellFactor_le_bound M omega hj T p
  · exact ((integrable_shellEnvelope M).mul_const _).const_mul _
  · refine Filter.Eventually.of_forall fun omega => ?_
    exact tendsto_kuhnDirichletInf_atBot (isOpenBoundedConvexDomain_openCarrier T)
      hUQ (continuous_shellFactor M 0 omega)
      (fun x => (shellFactor_pos M 0 omega x).le) p

theorem tendsto_qRSlope (M : GMCModel d) {T : KuhnCell d}
    (hT : T.supportCube = originCube d 0) (p : Vec d) :
    Filter.Tendsto (fun j : ℤ => qRSlope M (unitMesh d j) T p) Filter.atBot
      (nhds (qStarSlope M T p)) := by
  rw [qStarSlope_eq_inv_mul]
  exact (tendsto_integral_kuhnDirichletInf_shellFactor M hT p).const_mul _

/-! ## The modulus in expectation -/

theorem qRSlope_le_young (M : GMCModel d) {T : KuhnCell d} {j : ℤ} (hj : j ≤ 0)
    {t : ℝ} (ht : 0 < t) (p p' : Vec d) :
    qRSlope M (unitMesh d j) T p' ≤ (1 + t) * qRSlope M (unitMesh d j) T p +
      (1 + t⁻¹) * vecNormSq (p' - p) *
        ∫ omega, shellEnvelope M omega ∂M.P.toMeasure := by
  have hvol : (0 : ℝ) < (volume T.openCarrier).toReal :=
    volume_toReal_pos (kuhnCellDomain T)
  have hS : ∀ V ∈ unitMesh d j, V.closedCarrier ⊆
      Metric.closedBall (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0)) :=
    fun V hV => closedCarrier_subset_of_mem_unitMesh hj hV
  have hintp := integrable_kuhnDirichletInf_shellFactor M hS T.openCarrier p
  have hintp' := integrable_kuhnDirichletInf_shellFactor M hS T.openCarrier p'
  have hintW := integrable_kuhnWeightSum_shellFactor M hj T
  have hdomInt : Integrable (fun omega : PotentialSample d =>
      (1 + t) * kuhnDirichletInf (shellFactor M 0 omega) (unitMesh d j)
          T.openCarrier p +
        (1 + t⁻¹) * vecNormSq (p' - p) *
          kuhnWeightSum (shellFactor M 0 omega) (unitMesh d j) T.openCarrier)
      M.P.toMeasure :=
    (hintp.const_mul _).add (hintW.const_mul _)
  have hle := integral_mono hintp' hdomInt fun omega =>
    kuhnDirichletInf_le_young (continuous_shellFactor M 0 omega)
      (fun x => (shellFactor_pos M 0 omega x).le) ht p p'
  rw [integral_add (hintp.const_mul _) (hintW.const_mul _), integral_const_mul,
    integral_const_mul] at hle
  have hWle : ∫ omega, kuhnWeightSum (shellFactor M 0 omega) (unitMesh d j)
      T.openCarrier ∂M.P.toMeasure ≤
      (∫ omega, shellEnvelope M omega ∂M.P.toMeasure) *
        volume.real T.openCarrier := by
    have h := integral_mono hintW ((integrable_shellEnvelope M).mul_const _)
      fun omega => kuhnWeightSum_shellFactor_le M omega hj T
    rwa [integral_mul_const] at h
  have hcoef : (0 : ℝ) ≤ (1 + t⁻¹) * vecNormSq (p' - p) := by
    have : (0 : ℝ) < 1 + t⁻¹ := by positivity
    exact mul_nonneg this.le (vecNormSq_nonneg _)
  have hstep : ∫ omega, kuhnDirichletInf (shellFactor M 0 omega) (unitMesh d j)
      T.openCarrier p' ∂M.P.toMeasure ≤
      (1 + t) * ∫ omega, kuhnDirichletInf (shellFactor M 0 omega) (unitMesh d j)
        T.openCarrier p ∂M.P.toMeasure +
      (1 + t⁻¹) * vecNormSq (p' - p) *
        ((∫ omega, shellEnvelope M omega ∂M.P.toMeasure) *
          volume.real T.openCarrier) := by
    refine hle.trans ?_
    linarith [mul_le_mul_of_nonneg_left hWle hcoef]
  rw [qRSlope, qRSlope]
  have hmul := mul_le_mul_of_nonneg_left hstep
    (le_of_lt (inv_pos.mpr hvol))
  refine hmul.trans (le_of_eq ?_)
  have hv : (volume T.openCarrier).toReal ≠ 0 := ne_of_gt hvol
  have hreal : volume.real T.openCarrier = (volume T.openCarrier).toReal := rfl
  rw [hreal]
  field_simp

/-! ## Uniformity on the unit sphere -/

theorem qStarSlope_nonneg (M : GMCModel d) (T : KuhnCell d) (p : Vec d) :
    0 ≤ qStarSlope M T p := by
  rw [qStarSlope_eq_inv_mul]
  refine mul_nonneg (by positivity) (integral_nonneg fun omega => ?_)
  exact dirichletInfOn_nonneg (isOpen_openCarrier T).measurableSet
    fun x => (shellFactor_pos M 0 omega x).le

theorem qStarCell_nonneg (M : GMCModel d) (T : KuhnCell d) : 0 ≤ qStarCell M T := by
  obtain ⟨p, hp, hqeq⟩ := exists_mem_vecUnitSphere_qStarCell_eq M T
  rw [hqeq]
  exact qStarSlope_nonneg M T p



theorem exists_scale_forall_qRSlope_le (M : GMCModel d) {T : KuhnCell d}
    (hT : T.supportCube = originCube d 0) {eps : ℝ} (heps : 0 < eps) :
    ∃ j₀ : ℤ, j₀ ≤ 0 ∧ ∀ j ≤ j₀, ∀ p ∈ vecUnitSphere d,
      qRSlope M (unitMesh d j) T p ≤ qStarCell M T + eps := by
  classical
  set qs : ℝ := qStarCell M T with hqs
  have hqs0 : 0 ≤ qs := qStarCell_nonneg M T
  set G : ℝ := ∫ omega, shellEnvelope M omega ∂M.P.toMeasure with hG
  have hG0 : 0 ≤ G := integral_nonneg fun omega => (shellEnvelope_pos M omega).le
  -- the three small parameters
  set t : ℝ := eps / (3 * (qs + 1)) with ht'
  have ht : 0 < t := by positivity
  have htq : t * qs ≤ eps / 3 := by
    rw [ht', div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hqs0, heps.le]
  set eta : ℝ := eps / (3 * (1 + t)) with heta'
  have heta : 0 < eta := by positivity
  have hetastep : (1 + t) * eta = eps / 3 := by
    rw [heta']
    field_simp
  set delta : ℝ := eps / (3 * ((1 + t⁻¹) * G + 1)) with hdelta'
  have hden : (0 : ℝ) < 3 * ((1 + t⁻¹) * G + 1) := by positivity
  have hdelta : 0 < delta := by positivity
  have hdeltastep : (1 + t⁻¹) * delta * G ≤ eps / 3 := by
    have hA : (0 : ℝ) ≤ (1 + t⁻¹) * G := mul_nonneg (by positivity) hG0
    rw [hdelta', show (1 + t⁻¹) * (eps / (3 * ((1 + t⁻¹) * G + 1))) * G
        = ((1 + t⁻¹) * G) * eps / (3 * ((1 + t⁻¹) * G + 1)) by ring,
      div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 3)]
    nlinarith [hA, heps.le]
  -- the finite cover of the unit sphere
  have hopen : ∀ q : Vec d, IsOpen {p : Vec d | vecNormSq (p - q) < delta} := fun q =>
    isOpen_lt (continuous_vecNormSq.comp (continuous_id.sub continuous_const))
      continuous_const
  have hcover : vecUnitSphere d ⊆
      ⋃ q ∈ vecUnitSphere d, {p : Vec d | vecNormSq (p - q) < delta} := by
    intro p hp
    refine Set.mem_iUnion₂.mpr ⟨p, hp, ?_⟩
    simp [vecNormSq, vecDot, hdelta]
  obtain ⟨F, hFsub, hFfin, hFcover⟩ :=
    isCompact_vecUnitSphere.elim_finite_subcover_image (fun q _ => hopen q) hcover
  -- pointwise convergence at the finitely many centres
  have hpt : ∀ q ∈ F, ∀ᶠ j : ℤ in Filter.atBot,
      qRSlope M (unitMesh d j) T q < qStarSlope M T q + eta := by
    intro q _
    exact (tendsto_qRSlope M hT q).eventually
      (eventually_lt_nhds (by linarith : qStarSlope M T q < qStarSlope M T q + eta))
  have hall : ∀ᶠ j : ℤ in Filter.atBot, ∀ q ∈ F,
      qRSlope M (unitMesh d j) T q < qStarSlope M T q + eta :=
    (Filter.eventually_all_finite hFfin).mpr hpt
  obtain ⟨j₁, hj₁⟩ := Filter.eventually_atBot.mp hall
  refine ⟨min j₁ 0, min_le_right _ _, fun j hj p hp => ?_⟩
  have hj0 : j ≤ 0 := le_trans hj (min_le_right _ _)
  have hj1 : j ≤ j₁ := le_trans hj (min_le_left _ _)
  obtain ⟨q, hqF, hqp⟩ : ∃ q ∈ F, vecNormSq (p - q) < delta := by
    obtain ⟨s, hs, hps⟩ := Set.mem_iUnion₂.mp (hFcover hp)
    exact ⟨s, hs, hps⟩
  have hqsphere : q ∈ vecUnitSphere d := hFsub hqF
  have hqlt := hj₁ j hj1 q hqF
  have hqstar : qStarSlope M T q ≤ qs := qStarSlope_le_qStarCell M T hqsphere
  have hmod := qRSlope_le_young M (T := T) hj0 ht q p
  have hcoef : (0 : ℝ) < 1 + t⁻¹ := by positivity
  have hlast : (1 + t⁻¹) * vecNormSq (p - q) * G ≤ eps / 3 := by
    refine le_trans ?_ hdeltastep
    refine mul_le_mul_of_nonneg_right ?_ hG0
    exact mul_le_mul_of_nonneg_left hqp.le hcoef.le
  have hfirst : (1 + t) * qRSlope M (unitMesh d j) T q ≤ qs + 2 * (eps / 3) := by
    have h1 : qRSlope M (unitMesh d j) T q ≤ qs + eta := by linarith
    have h2 : (1 + t) * (qs + eta) = qs + t * qs + (1 + t) * eta := by ring
    have h3 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + t)
    rw [h2, hetastep] at h3
    linarith
  linarith [hmod, hfirst, hlast]

/-! ## The lower bound `q_* <= q_R` -/

theorem shellFactor_le_shellEnvelope (M : GMCModel d) (omega : PotentialSample d)
    {T : KuhnCell d} (hT : T.supportCube = originCube d 0) {x : Vec d}
    (hx : x ∈ T.closedCarrier) :
    shellFactor M 0 omega x ≤ shellEnvelope M omega := by
  have hball : x ∈ Metric.closedBall (cubeCenter (originCube d 0))
      (cubeRadius (originCube d 0)) := by
    have h := T.closedCarrier_subset_closedBall hx
    rwa [hT] at h
  have habs := abs_apply_le_g2Observable_of_mem_closedBall (omega 0) hball
  have hle : omega 0 x ≤ |omega 0 x| := le_abs_self _
  exact Real.exp_le_exp.mpr (by linarith)



theorem qStarSlope_le_qRSlope (M : GMCModel d) {T : KuhnCell d}
    (hT : T.supportCube = originCube d 0) {j : ℤ} (hj : j ≤ 0) (p : Vec d) :
    qStarSlope M T p ≤ qRSlope M (unitMesh d j) T p := by
  have hUmeas : MeasurableSet T.openCarrier := (isOpen_openCarrier T).measurableSet
  have hUvol : volume T.openCarrier < ⊤ := (isBounded_openCarrier T).measure_lt_top
  haveI : IsFiniteMeasure (volume.restrict T.openCarrier) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hUvol⟩
  have hS : ∀ V ∈ unitMesh d j, V.closedCarrier ⊆
      Metric.closedBall (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0)) :=
    fun V hV => closedCarrier_subset_of_mem_unitMesh hj hV
  have hjQ : j ≤ (originCube d 0).scale := hj
  have hcover : T.openCarrier ⊆
      ⋃ V ∈ (unitMesh d j : Set (KuhnCell d)), V.carrier := by
    intro x hx
    rw [unitMesh, ← cubeSet_eq_iUnion_triadicSimplexPartition (originCube d 0) hjQ]
    refine openCubeSet_subset_cubeSet _ ?_
    have h := T.openCarrier_subset_openCubeSet hx
    rwa [hT] at h
  rw [qStarSlope_eq_inv_mul, qRSlope]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine integral_mono (integrable_dirichletInfOn_shellFactor M T p)
    (integrable_kuhnDirichletInf_shellFactor M hS T.openCarrier p) fun omega => ?_
  refine dirichletInfOn_le_kuhnDirichletInf (C := shellEnvelope M omega) hUmeas
    (ne_of_lt hUvol)
    (fun V hV => supportCube_scale_eq_of_mem_triadicSimplexPartition hjQ hV) hcover
    (continuous_shellFactor M 0 omega)
    (fun x => (shellFactor_pos M 0 omega x).le) fun x hx => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (shellFactor_pos M 0 omega x).le]
  exact shellFactor_le_shellEnvelope M omega hT (T.openCarrier_subset_closedCarrier hx)

/-! ## The selection of `R` -/

theorem qRCell_le_of_forall (M : GMCModel d) (S : Finset (KuhnCell d))
    (T : KuhnCell d) {c : ℝ} (hd : 0 < d)
    (h : ∀ p ∈ vecUnitSphere d, qRSlope M S T p ≤ c) : qRCell M S T ≤ c := by
  refine csSup_le ((vecUnitSphere_nonempty hd).image _) ?_
  rintro y ⟨p, hp, rfl⟩
  exact h p hp

theorem qStarCell_le_qRCell (M : GMCModel d) {T : KuhnCell d}
    (hT : T.supportCube = originCube d 0) {j : ℤ} (hj : j ≤ 0) :
    qStarCell M T ≤ qRCell M (unitMesh d j) T := by
  obtain ⟨p, hp, hqeq⟩ := exists_mem_vecUnitSphere_qStarCell_eq M T
  rw [hqeq]
  exact le_trans (qStarSlope_le_qRSlope M hT hj p)
    (qRSlope_le_qRCell M (fun V hV => closedCarrier_subset_of_mem_unitMesh hj hV) T hp)



theorem tendsto_qRCell (M : GMCModel d) {T : KuhnCell d}
    (hT : T.supportCube = originCube d 0) :
    Filter.Tendsto (fun j : ℤ => qRCell M (unitMesh d j) T) Filter.atBot
      (nhds (qStarCell M T)) := by
  have hd : 0 < d := lt_of_lt_of_le two_pos M.shellPrefix.dimension
  refine Metric.tendsto_nhds.mpr fun eps heps => ?_
  obtain ⟨j₀, hj₀, hbound⟩ := exists_scale_forall_qRSlope_le M hT (half_pos heps)
  filter_upwards [Filter.eventually_le_atBot j₀] with j hj
  have hj0 : j ≤ 0 := le_trans hj hj₀
  have hup : qRCell M (unitMesh d j) T ≤ qStarCell M T + eps / 2 :=
    qRCell_le_of_forall M _ T hd (hbound j hj)
  have hlow := qStarCell_le_qRCell M hT hj0
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [half_lt_self heps]



theorem exists_pos_qRCell_lt_one (M : GMCModel d) {T : KuhnCell d}
    (hT : T.supportCube = originCube d 0) :
    ∃ R : ℕ, 0 < R ∧ qRCell M (unitMesh d (-(R : ℤ))) T < 1 := by
  have hd : 0 < d := lt_of_lt_of_le two_pos M.shellPrefix.dimension
  have hlt : qStarCell M T < 1 := qStarCell_lt_one M T
  set eps : ℝ := (1 - qStarCell M T) / 2 with heps'
  have heps : 0 < eps := by rw [heps']; linarith
  obtain ⟨j₀, hj₀, hbound⟩ := exists_scale_forall_qRSlope_le M hT heps
  set R : ℕ := (1 - j₀).toNat with hR
  have hRpos : 0 < R := by
    rw [hR]
    omega
  have hjR : -(R : ℤ) ≤ j₀ := by
    rw [hR]
    omega
  refine ⟨R, hRpos, ?_⟩
  refine lt_of_le_of_lt (qRCell_le_of_forall M _ T hd
    (hbound _ hjR)) ?_
  rw [heps']
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
