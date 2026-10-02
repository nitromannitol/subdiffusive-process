import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DiscreteDirichletInfimum
import Homogenization.Sobolev.Foundations.DifferenceQuotient




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Kuhn MeasureTheory Metric Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Two bridges -/

/-- **Weak gradients of one function agree almost everywhere.**  Needed because
(S2a) returns an `H^1` representative with a pointwise cellwise gradient and,
separately, an `H_0^1` witness for the same `toFun`. -/
theorem H1Function.grad_ae_eq_of_toFun_eq {U : Set (Vec d)} (hU : IsOpen U)
    {u v : H1Function U} (huv : u.toFun = v.toFun) :
    u.grad =ᵐ[volume.restrict U] v.grad := by
  have hcoord : ∀ i : Fin d,
      (fun x => u.grad x i) =ᵐ[volume.restrict U] fun x => v.grad x i := by
    intro i
    refine HasWeakPartialDerivOn.ae_eq hU
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((u.gradMemL2 i).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)))
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((v.gradMemL2 i).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)))
      (u.hasWeakGradient i) ?_
    rw [huv]
    exact v.hasWeakGradient i
  have hall : ∀ᵐ x ∂(volume.restrict U), ∀ i : Fin d, u.grad x i = v.grad x i :=
    MeasureTheory.ae_all_iff.mpr hcoord
  filter_upwards [hall] with x hx
  funext i
  exact hx i

/-- **From `eLpNorm` to the real `L^2` norm.**  (S2a) states its estimate through
`eLpNorm`; every energy comparison is a real integral. -/
theorem integral_vecNormSq_sub_grad_le_of_eLpNorm_le {U : Set (Vec d)}
    {v w : H1Function U} {eps : ℝ} (heps : 0 ≤ eps)
    (h : ∀ i : Fin d, eLpNorm (fun x => v.grad x i - w.grad x i) 2
      (volume.restrict U) ≤ ENNReal.ofReal eps) :
    (∫ x in U, vecNormSq (v.grad x - w.grad x)) ≤ (d : ℝ) * eps ^ 2 := by
  have hmem : ∀ i : Fin d,
      MemLp (fun x => v.grad x i - w.grad x i) 2 (volume.restrict U) :=
    fun i => (v.gradMemL2 i).sub (w.gradMemL2 i)
  have hcoord : ∀ i : Fin d,
      (∫ x in U, (v.grad x i - w.grad x i) ^ 2) ≤ eps ^ 2 := by
    intro i
    rw [← toReal_eLpNorm_two_sq_eq_integral_sq (hmem i)]
    have hle : (eLpNorm (fun x => v.grad x i - w.grad x i) 2
        (volume.restrict U)).toReal ≤ eps :=
      ENNReal.toReal_le_of_le_ofReal heps (h i)
    nlinarith [ENNReal.toReal_nonneg
      (a := eLpNorm (fun x => v.grad x i - w.grad x i) 2 (volume.restrict U))]
  have hsplit : (∫ x in U, vecNormSq (v.grad x - w.grad x)) =
      ∑ i : Fin d, ∫ x in U, (v.grad x i - w.grad x i) ^ 2 := by
    rw [← integral_finset_sum Finset.univ fun i _ => (hmem i).integrable_sq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [vecNormSq, vecDot, pow_two]
  rw [hsplit]
  calc ∑ i : Fin d, ∫ x in U, (v.grad x i - w.grad x i) ^ 2
      ≤ ∑ _i : Fin d, eps ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
    _ = (d : ℝ) * eps ^ 2 := by simp

/-! ## The upper half of (S2c) -/

/-- **(S2c), upper half.**  For every `eps > 0` there is a mesh scale below which
*every* mesh of the ambient cube has `Q_{R,pi}(p)` within `eps` of the continuum
minimum from above.

The proof is the source's, in three moves: pick a continuum competitor `w`
within `eps/3` of the infimum; replace it by a conforming piecewise-affine `v`
whose gradient is `L^2`-close, at an energy cost bounded by the Cauchy-Schwarz
step of `DirichletEnergyContinuity.lean`; and replace `B` by its cellwise
supremum, at a cost bounded by the uniform envelope error of (S2b).  The last
two costs are made `eps/3` each, and the passage from the single scale that
(S2a) returns to all finer scales is `KuhnCompetitor.refineMesh`. -/
theorem exists_scale_forall_kuhnDirichletInf_le {n : ℕ} {Q : TriadicCube (n + 1)}
    {U : Set (Vec (n + 1))} {B : Vec (n + 1) → ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hUQ : U ⊆ openCubeSet Q)
    (hB : Continuous B) (hB0 : ∀ x, 0 ≤ B x) (p : Vec (n + 1)) {eps : ℝ}
    (heps : 0 < eps) :
    ∃ j₀ : ℤ, j₀ ≤ Q.scale ∧ ∀ j : ℤ, j ≤ j₀ →
      kuhnDirichletInf B (triadicSimplexPartition Q j) U p ≤
        dirichletInfOn B U p + eps := by
  classical
  have hUopen : IsOpen U := hU.isOpen
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hUvol : volume U < ⊤ := hU.isBoundedDomain.volume_lt_top
  have hUfin : volume U ≠ ⊤ := ne_of_lt hUvol
  haveI : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hUvol⟩
  -- a uniform bound for the coefficient on the ambient closed cube
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
      hB.continuousOn
  set C : ℝ := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hUball : U ⊆ closedBall (cubeCenter Q) (cubeRadius Q) :=
    (hUQ.trans (openCubeSet_subset_cubeSet Q)).trans (cubeSet_subset_closedBall Q)
  have hCU : ∀ x ∈ U, ‖B x‖ ≤ C := fun x hx =>
    (hC₀ x (hUball hx)).trans (le_max_left _ _)
  have hCU' : ∀ x ∈ U, |B x| ≤ C := hCU
  -- a near-optimal continuum competitor
  obtain ⟨E, ⟨w, rfl⟩, hw⟩ :=
    exists_lt_of_csInf_lt (dirichletEnergySet_nonempty B U p)
      (lt_add_of_pos_right (dirichletInfOn B U p) (by linarith : (0 : ℝ) < eps / 3))
  set Dw : Vec (n + 1) → Vec (n + 1) := w.toH1Function.grad with hDw
  have hnormw : IntegrableOn (fun x => vecNormSq (p + Dw x)) U volume :=
    integrableOn_vecNormSq_add_grad w.toH1Function p
  set W : ℝ := ∫ x in U, vecNormSq (p + Dw x) with hW
  have hW0 : 0 ≤ W := setIntegral_nonneg hUmeas fun _ _ => vecNormSq_nonneg _
  set M : ℝ := Real.sqrt (6 * W + 4) with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hCM : 0 ≤ C * M := mul_nonneg hC0 hM0
  -- the two small parameters
  set delta : ℝ := min 1 (eps / (3 * (C * M + 1))) with hdeltadef
  have hdelta : 0 < delta := lt_min one_pos (by positivity)
  have hdelta1 : delta ≤ 1 := min_le_left _ _
  have hdelta2 : delta ≤ eps / (3 * (C * M + 1)) := min_le_right _ _
  have hstep : C * (delta * M) ≤ eps / 3 := by
    have hpos : (0 : ℝ) < 3 * (C * M + 1) := by positivity
    have h : delta * (3 * (C * M + 1)) ≤ eps := (le_div_iff₀ hpos).mp hdelta2
    nlinarith [hdelta.le, hCM]
  set eta : ℝ := eps / (3 * (2 * W + 3)) with hetadef
  have heta : 0 < eta := by positivity
  have hetastep : eta * (2 * W + 2) ≤ eps / 3 := by
    rw [hetadef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [heps.le, hW0]
  -- (S2a): a conforming competitor with `L^2`-close gradient
  obtain ⟨j₁, phi, v, hj₁Q, hv10, -, hcell, hvapprox⟩ :=
    exists_kuhn_h10_approx hU hUQ w (eps := delta / (n + 1))
      (by positivity)
  obtain ⟨v0, hv0⟩ := hv10
  have hgradae : v0.toH1Function.grad =ᵐ[volume.restrict U] v.grad :=
    H1Function.grad_ae_eq_of_toFun_eq hUopen hv0
  have hconf : IsCellwiseSlope (triadicSimplexPartition Q j₁) U
      v0.toH1Function.grad (fun T => kuhnSlope T phi) :=
    IsCellwiseSlope.congr (isCellwiseSlope_of_forall_mem_openCarrier hUmeas hcell)
      hgradae
  set c₁ : KuhnCompetitor U (triadicSimplexPartition Q j₁) :=
    ⟨v0, fun T => kuhnSlope T phi, hconf⟩ with hc₁
  -- the `L^2` distance to the continuum competitor
  have hdiffint : IntegrableOn (fun x => vecNormSq (c₁.grad x - Dw x)) U volume :=
    integrableOn_vecNormSq_sub_grad v0.toH1Function w.toH1Function
  have hdiffL2 : (∫ x in U, vecNormSq (c₁.grad x - Dw x)) ≤ delta ^ 2 := by
    have hap : ∀ i : Fin (n + 1),
        eLpNorm (fun x => v0.toH1Function.grad x i - Dw x i) 2 (volume.restrict U) ≤
          ENNReal.ofReal (delta / (n + 1)) := by
      intro i
      refine le_of_le_of_eq ?_ rfl
      refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) (hvapprox i)
      filter_upwards [hgradae] with x hx
      rw [hx]
    have hbase := integral_vecNormSq_sub_grad_le_of_eLpNorm_le
      (v := v0.toH1Function) (w := w.toH1Function) (by positivity) hap
    refine hbase.trans ?_
    have hrw : ((n + 1 : ℕ) : ℝ) * (delta / ((n : ℕ) + 1)) ^ 2 =
        delta ^ 2 / ((n : ℝ) + 1) := by
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
    rw [hrw]
    exact div_le_self (sq_nonneg delta) (by simp)
  -- the `L^2` size of the discrete competitor
  have hnormc : IntegrableOn (fun x => vecNormSq (p + c₁.grad x)) U volume :=
    integrableOn_vecNormSq_add_grad v0.toH1Function p
  have hAeq : (fun x => vecNormSq (p + c₁.grad x)) =
      fun x => vecNormSq ((p + Dw x) + (c₁.grad x - Dw x)) := by
    funext x
    congr 1
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hA : (∫ x in U, vecNormSq (p + c₁.grad x)) ≤ 2 * W + 2 := by
    have hcomb := integral_vecNormSq_add_le (U := U) (F := fun x => p + Dw x)
      (G := fun x => c₁.grad x - Dw x) hUmeas hnormw hdiffint (by rw [← hAeq]; exact hnormc)
    rw [← hAeq] at hcomb
    nlinarith [hdiffL2, hdelta1, hdelta.le, hW0]
  have hsumint : IntegrableOn
      (fun x => vecNormSq (p + c₁.grad x + (p + Dw x))) U volume :=
    integrableOn_vecNormSq_of_memLp fun i =>
      ((memLp_const (p i)).add (v0.toH1Function.gradMemL2 i)).add
        ((memLp_const (p i)).add (w.toH1Function.gradMemL2 i))
  have hS : (∫ x in U, vecNormSq (p + c₁.grad x + (p + Dw x))) ≤ 6 * W + 4 := by
    have hcomb := integral_vecNormSq_add_le (U := U) (F := fun x => p + c₁.grad x)
      (G := fun x => p + Dw x) hUmeas hnormc hnormw hsumint
    nlinarith [hA, hW0]
  -- the Cauchy-Schwarz transport
  have hintw : IntegrableOn (fun x => B x * vecNormSq (p + Dw x)) U volume :=
    integrableOn_mul_of_integrableOn_vecNormSq hUmeas hB.measurable hCU hnormw
  have hintc : IntegrableOn (fun x => B x * vecNormSq (p + c₁.grad x)) U volume :=
    integrableOn_mul_of_integrableOn_vecNormSq hUmeas hB.measurable hCU hnormc
  have hl2diff : l2NormOn U (fun x => c₁.grad x - Dw x) ≤ delta := by
    rw [l2NormOn]
    calc Real.sqrt (∫ x in U, vecNormSq (c₁.grad x - Dw x))
        ≤ Real.sqrt (delta ^ 2) := Real.sqrt_le_sqrt hdiffL2
      _ = delta := Real.sqrt_sq hdelta.le
  have hl2sum : l2NormOn U (fun x => p + c₁.grad x + (p + Dw x)) ≤ M := by
    rw [l2NormOn, hM]
    exact Real.sqrt_le_sqrt hS
  have hcont : |dirichletEnergyOn' B U p c₁.grad - dirichletEnergyOn' B U p Dw| ≤
      eps / 3 := by
    refine le_trans (abs_dirichletEnergyOn'_sub_le hUmeas hC0 hCU' hintc hintw
      hdiffint hsumint) (le_trans ?_ hstep)
    refine mul_le_mul_of_nonneg_left ?_ hC0
    exact mul_le_mul hl2diff hl2sum (l2NormOn_nonneg _ _) hdelta.le
  -- (S2b): the envelope error
  obtain ⟨s₀, hs₀⟩ :=
    abs_kuhnEnvelope_sub_le_of_scale_le hB
      (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)) heta
  refine ⟨min (min j₁ s₀) Q.scale, min_le_right _ _, fun j hj => ?_⟩
  have hjQ : j ≤ Q.scale := le_trans hj (min_le_right _ _)
  have hj₁ : j ≤ j₁ := le_trans hj (le_trans (min_le_left _ _) (min_le_left _ _))
  have hjs₀ : j ≤ s₀ := le_trans hj (le_trans (min_le_left _ _) (min_le_right _ _))
  set S : Finset (KuhnCell (n + 1)) := triadicSimplexPartition Q j with hS'
  have hscale : ∀ T ∈ S, T.supportCube.scale = j := fun T hT =>
    supportCube_scale_eq_of_mem_triadicSimplexPartition hjQ hT
  have hcellsub : ∀ T ∈ S, T.closedCarrier ⊆ closedBall (cubeCenter Q) (cubeRadius Q) :=
    fun T hT => closedCarrier_subset_closedBall_of_mem_triadicSimplexPartition hjQ hT
  have hcover : U ⊆ ⋃ T ∈ (S : Set (KuhnCell (n + 1))), T.carrier := by
    intro x hx
    rw [← cubeSet_eq_iUnion_triadicSimplexPartition Q hjQ]
    exact openCubeSet_subset_cubeSet Q (hUQ hx)
  have hclose : ∀ T ∈ S, ∀ x ∈ T.openCarrier, |cellSup B T - B x| ≤ eta := by
    intro T hT x hx
    have hxc : x ∈ T.carrier := T.openCarrier_subset_carrier hx
    have h := hs₀ S j hjs₀ hscale hcellsub T hT x hxc
    rwa [kuhnEnvelope_of_mem_carrier hscale B hT hxc] at h
  -- the refined competitor
  set c : KuhnCompetitor U S := c₁.refineMesh hj₁Q hj₁ with hc
  have hcgrad : c.grad = c₁.grad := rfl
  have hintc' : IntegrableOn (fun x => B x * vecNormSq (p + c.grad x)) U volume := by
    rw [hcgrad]; exact hintc
  have hnormc' : IntegrableOn (fun x => vecNormSq (p + c.grad x)) U volume := by
    rw [hcgrad]; exact hnormc
  have henv := abs_kuhnDiscreteEnergy_sub_dirichletEnergyOn'_le hUmeas hscale hcover
    hclose c hintc' hnormc'
  rw [hcgrad] at henv
  have hetaA : eta * (∫ x in U, vecNormSq (p + c₁.grad x)) ≤ eps / 3 :=
    le_trans (mul_le_mul_of_nonneg_left hA heta.le) hetastep
  have hQ : kuhnDirichletInf B S U p ≤ kuhnDiscreteEnergy B S U p c.slope :=
    kuhnDirichletInf_le hB hB0 p c
  have habs := abs_le.mp henv
  have hcont' := abs_le.mp hcont
  linarith [hQ, habs.2, hcont'.2, hetaA, hw]

/-! ## (S2c) -/



theorem tendsto_kuhnDirichletInf_atBot {n : ℕ} {Q : TriadicCube (n + 1)}
    {U : Set (Vec (n + 1))} {B : Vec (n + 1) → ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hUQ : U ⊆ openCubeSet Q)
    (hB : Continuous B) (hB0 : ∀ x, 0 ≤ B x) (p : Vec (n + 1)) :
    Filter.Tendsto
      (fun j : ℤ => kuhnDirichletInf B (triadicSimplexPartition Q j) U p)
      Filter.atBot (nhds (dirichletInfOn B U p)) := by
  have hUopen : IsOpen U := hU.isOpen
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hUvol : volume U < ⊤ := hU.isBoundedDomain.volume_lt_top
  have hUfin : volume U ≠ ⊤ := ne_of_lt hUvol
  haveI : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hUvol⟩
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
      hB.continuousOn
  have hUball : U ⊆ closedBall (cubeCenter Q) (cubeRadius Q) :=
    (hUQ.trans (openCubeSet_subset_cubeSet Q)).trans (cubeSet_subset_closedBall Q)
  have hCU : ∀ x ∈ U, ‖B x‖ ≤ C₀ := fun x hx => hC₀ x (hUball hx)
  refine Metric.tendsto_nhds.mpr fun eps heps => ?_
  obtain ⟨j₀, hj₀Q, hj₀⟩ :=
    exists_scale_forall_kuhnDirichletInf_le hU hUQ hB hB0 p (half_pos heps)
  filter_upwards [Filter.eventually_le_atBot j₀] with j hj
  have hjQ : j ≤ Q.scale := le_trans hj hj₀Q
  have hlow : dirichletInfOn B U p ≤
      kuhnDirichletInf B (triadicSimplexPartition Q j) U p := by
    refine dirichletInfOn_le_kuhnDirichletInf (C := C₀) hUmeas hUfin
      (fun T hT => supportCube_scale_eq_of_mem_triadicSimplexPartition hjQ hT)
      ?_ hB hB0 hCU
    intro x hx
    rw [← cubeSet_eq_iUnion_triadicSimplexPartition Q hjQ]
    exact openCubeSet_subset_cubeSet Q (hUQ hx)
  have hup := hj₀ j hj
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [half_lt_self heps]



theorem dirichletInfOn_eq_iInf_kuhnDirichletInf {n : ℕ} {Q : TriadicCube (n + 1)}
    {U : Set (Vec (n + 1))} {B : Vec (n + 1) → ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hUQ : U ⊆ openCubeSet Q)
    (hB : Continuous B) (hB0 : ∀ x, 0 ≤ B x) (p : Vec (n + 1)) :
    dirichletInfOn B U p =
      ⨅ j : ℤ, kuhnDirichletInf B (triadicSimplexPartition Q (min j Q.scale)) U p := by
  have hUopen : IsOpen U := hU.isOpen
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hUvol : volume U < ⊤ := hU.isBoundedDomain.volume_lt_top
  have hUfin : volume U ≠ ⊤ := ne_of_lt hUvol
  haveI : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hUvol⟩
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
      hB.continuousOn
  have hUball : U ⊆ closedBall (cubeCenter Q) (cubeRadius Q) :=
    (hUQ.trans (openCubeSet_subset_cubeSet Q)).trans (cubeSet_subset_closedBall Q)
  have hCU : ∀ x ∈ U, ‖B x‖ ≤ C₀ := fun x hx => hC₀ x (hUball hx)
  have hlow : ∀ j : ℤ, dirichletInfOn B U p ≤
      kuhnDirichletInf B (triadicSimplexPartition Q (min j Q.scale)) U p := by
    intro j
    have hjQ : min j Q.scale ≤ Q.scale := min_le_right _ _
    refine dirichletInfOn_le_kuhnDirichletInf (C := C₀) hUmeas hUfin
      (fun T hT => supportCube_scale_eq_of_mem_triadicSimplexPartition hjQ hT)
      ?_ hB hB0 hCU
    intro x hx
    rw [← cubeSet_eq_iUnion_triadicSimplexPartition Q hjQ]
    exact openCubeSet_subset_cubeSet Q (hUQ hx)
  refine le_antisymm (le_ciInf hlow) ?_
  refine le_of_forall_pos_le_add fun eps heps => ?_
  obtain ⟨j₀, hj₀Q, hj₀⟩ :=
    exists_scale_forall_kuhnDirichletInf_le hU hUQ hB hB0 p heps
  refine le_trans (ciInf_le ⟨dirichletInfOn B U p, ?_⟩ j₀) ?_
  · rintro y ⟨j, rfl⟩
    exact hlow j
  · exact hj₀ _ (le_of_eq (min_eq_left hj₀Q))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
