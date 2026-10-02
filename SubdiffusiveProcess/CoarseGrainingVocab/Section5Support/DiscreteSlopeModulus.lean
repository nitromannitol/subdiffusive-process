import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DiscreteDirichletInfimum




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Kuhn MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## Young's inequality for the ambient quadratic form -/

theorem vecNormSq_add_expand (a b : Vec d) :
    vecNormSq (a + b) = vecNormSq a + 2 * vecDot a b + vecNormSq b := by
  simp only [vecNormSq, vecDot, Pi.add_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem two_vecDot_le_of_pos {t : ℝ} (ht : 0 < t) (a b : Vec d) :
    2 * vecDot a b ≤ t * vecNormSq a + t⁻¹ * vecNormSq b := by
  simp only [vecNormSq, vecDot, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hkey : t * (a i * a i) + b i * b i / t - 2 * (a i * b i) =
      (t * a i - b i) ^ 2 / t := by
    field_simp
    ring
  have hnn : 0 ≤ (t * a i - b i) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have hinv : t⁻¹ * (b i * b i) = b i * b i / t := by ring
  linarith [hkey, hnn, hinv]

/-- **Young's inequality for the ambient quadratic form.**  This is the single
algebraic input behind the mesh-uniform modulus. -/
theorem vecNormSq_add_le_young {t : ℝ} (ht : 0 < t) (a b : Vec d) :
    vecNormSq (a + b) ≤ (1 + t) * vecNormSq a + (1 + t⁻¹) * vecNormSq b := by
  have h := two_vecDot_le_of_pos ht a b
  rw [vecNormSq_add_expand]
  nlinarith [h]

/-! ## The total cell weight -/

/-- **`W = sum_T |T| sup_{closure T} B`**, the total weight of the discrete
energy.  It is the value of the discrete energy at the affine competitor and
unit slope, and the size of the modulus below. -/
def kuhnWeightSum (B : Vec d → ℝ) (S : Finset (KuhnCell d)) (U : Set (Vec d)) : ℝ :=
  ∑ T ∈ S, volume.real (U ∩ T.openCarrier) * cellSup B T

theorem kuhnWeightSum_nonneg {B : Vec d → ℝ} {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} (hB : Continuous B) (hB0 : ∀ x, 0 ≤ B x) :
    0 ≤ kuhnWeightSum B S U := by
  refine Finset.sum_nonneg fun T _ => mul_nonneg measureReal_nonneg ?_
  exact le_trans (hB0 (T.vertex 0))
    (le_cellSup T hB.continuousOn (T.vertex_mem_closedCarrier 0))

theorem kuhnDiscreteEnergy_eq_weight_mul {B : Vec d → ℝ} {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} (p : Vec d) :
    kuhnDiscreteEnergy B S U p 0 = vecNormSq p * kuhnWeightSum B S U := by
  rw [kuhnDiscreteEnergy, kuhnWeightSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [Pi.zero_apply, add_zero]
  ring



theorem kuhnDirichletInf_le_weightSum {B : Vec d → ℝ} {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} (hB : Continuous B) (hB0 : ∀ x, 0 ≤ B x) (p : Vec d) :
    kuhnDirichletInf B S U p ≤ vecNormSq p * kuhnWeightSum B S U := by
  have h := kuhnDirichletInf_le hB hB0 p (0 : KuhnCompetitor U S)
  have h0 : (0 : KuhnCompetitor U S).slope = 0 := rfl
  rw [h0, kuhnDiscreteEnergy_eq_weight_mul] at h
  exact h

/-! ## The modulus -/

theorem kuhnDiscreteEnergy_le_young {B : Vec d → ℝ} {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} (hB : Continuous B) (hB0 : ∀ x, 0 ≤ B x) {t : ℝ} (ht : 0 < t)
    (p p' : Vec d) (q : KuhnCell d → Vec d) :
    kuhnDiscreteEnergy B S U p' q ≤
      (1 + t) * kuhnDiscreteEnergy B S U p q +
        (1 + t⁻¹) * vecNormSq (p' - p) * kuhnWeightSum B S U := by
  rw [kuhnDiscreteEnergy, kuhnDiscreteEnergy, kuhnWeightSum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun T hT => ?_
  have hw : 0 ≤ volume.real (U ∩ T.openCarrier) * cellSup B T := by
    refine mul_nonneg measureReal_nonneg ?_
    exact le_trans (hB0 (T.vertex 0))
      (le_cellSup T hB.continuousOn (T.vertex_mem_closedCarrier 0))
  have hshift : p' + q T = (p + q T) + (p' - p) := by
    funext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
  have hyoung := vecNormSq_add_le_young ht (p + q T) (p' - p)
  rw [hshift]
  calc volume.real (U ∩ T.openCarrier) *
        (cellSup B T * vecNormSq (p + q T + (p' - p)))
      ≤ volume.real (U ∩ T.openCarrier) * (cellSup B T *
          ((1 + t) * vecNormSq (p + q T) + (1 + t⁻¹) * vecNormSq (p' - p))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hyoung ?_)
          measureReal_nonneg
        exact le_trans (hB0 (T.vertex 0))
          (le_cellSup T hB.continuousOn (T.vertex_mem_closedCarrier 0))
    _ = (1 + t) * (volume.real (U ∩ T.openCarrier) *
            (cellSup B T * vecNormSq (p + q T))) +
          (1 + t⁻¹) * vecNormSq (p' - p) *
            (volume.real (U ∩ T.openCarrier) * cellSup B T) := by ring



theorem kuhnDirichletInf_le_young {B : Vec d → ℝ} {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} (hB : Continuous B) (hB0 : ∀ x, 0 ≤ B x) {t : ℝ} (ht : 0 < t)
    (p p' : Vec d) :
    kuhnDirichletInf B S U p' ≤
      (1 + t) * kuhnDirichletInf B S U p +
        (1 + t⁻¹) * vecNormSq (p' - p) * kuhnWeightSum B S U := by
  refine le_of_forall_pos_le_add fun eps heps => ?_
  have ht1 : (0 : ℝ) < 1 + t := by linarith
  obtain ⟨c, hc⟩ := exists_kuhnCompetitor_kuhnDiscreteEnergy_lt B (S := S) (U := U) p
    (eps := eps / (1 + t)) (by positivity)
  have hstep := kuhnDiscreteEnergy_le_young (S := S) (U := U) hB hB0 ht p p' c.slope
  have hinf := kuhnDirichletInf_le hB hB0 p' c
  have hmul : (1 + t) * kuhnDiscreteEnergy B S U p c.slope ≤
      (1 + t) * kuhnDirichletInf B S U p + eps := by
    have := mul_le_mul_of_nonneg_left hc.le ht1.le
    have heq : (1 + t) * (kuhnDirichletInf B S U p + eps / (1 + t)) =
        (1 + t) * kuhnDirichletInf B S U p + eps := by
      field_simp
    linarith [this, heq.le, heq.ge]
  linarith [hinf, hstep, hmul]

/-! ## A mesh-uniform bound on the total weight -/

/-- **`W <= c |U|` whenever every cellwise supremum is at most `c`.**  The cells
of one mesh have pairwise disjoint interiors, so their total volume inside `U`
never exceeds `|U|`; the bound on the suprema is then the only mesh-dependent
input, and (g2) supplies one bound valid at every scale. -/
theorem kuhnWeightSum_le_mul {B : Vec d → ℝ} {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} {c : ℝ} (hU : MeasurableSet U) (hUfin : volume U ≠ ⊤)
    (hc0 : 0 ≤ c) (hc : ∀ T ∈ S, cellSup B T ≤ c)
    (hdisj : (S : Set (KuhnCell d)).PairwiseDisjoint KuhnCell.openCarrier) :
    kuhnWeightSum B S U ≤ c * volume.real U := by
  have hvol : ∑ T ∈ S, volume.real (U ∩ T.openCarrier) ≤ volume.real U := by
    have hmeas : ∀ T ∈ S, MeasurableSet (U ∩ T.openCarrier) := fun T _ =>
      hU.inter (isOpen_openCarrier T).measurableSet
    have hpair : (S : Set (KuhnCell d)).PairwiseDisjoint
        fun T => U ∩ T.openCarrier := fun T hT V hV hTV =>
      Disjoint.mono Set.inter_subset_right Set.inter_subset_right (hdisj hT hV hTV)
    have hsum : ∑ T ∈ S, volume (U ∩ T.openCarrier) =
        volume (⋃ T ∈ (S : Set (KuhnCell d)), (U ∩ T.openCarrier)) :=
      (measure_biUnion_finset hpair hmeas).symm
    have hsub : (⋃ T ∈ (S : Set (KuhnCell d)), (U ∩ T.openCarrier)) ⊆ U := by
      refine Set.iUnion₂_subset fun T _ => Set.inter_subset_left
    have hle : ∑ T ∈ S, volume (U ∩ T.openCarrier) ≤ volume U := by
      rw [hsum]
      exact measure_mono hsub
    have hfin : ∀ T ∈ S, volume (U ∩ T.openCarrier) ≠ ⊤ := fun T _ =>
      ne_top_of_le_ne_top hUfin (measure_mono Set.inter_subset_left)
    have htoReal : ∑ T ∈ S, volume.real (U ∩ T.openCarrier) =
        (∑ T ∈ S, volume (U ∩ T.openCarrier)).toReal := by
      rw [ENNReal.toReal_sum hfin]
      rfl
    rw [htoReal]
    exact ENNReal.toReal_mono hUfin hle
  calc kuhnWeightSum B S U
      ≤ ∑ T ∈ S, volume.real (U ∩ T.openCarrier) * c := by
        refine Finset.sum_le_sum fun T hT => ?_
        exact mul_le_mul_of_nonneg_left (hc T hT) measureReal_nonneg
    _ = (∑ T ∈ S, volume.real (U ∩ T.openCarrier)) * c := by
        rw [Finset.sum_mul]
    _ ≤ volume.real U * c := mul_le_mul_of_nonneg_right hvol hc0
    _ = c * volume.real U := mul_comm _ _

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
