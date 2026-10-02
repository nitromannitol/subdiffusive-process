import SubdiffusiveProcess.Main.InfraredPartialSum
import SubdiffusiveProcess.Sobolev.PotentialResponses
import SubdiffusiveProcess.Sobolev.GradientRange
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Lane3.ResamplingV2
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Lane4.Carriers
import Mathlib.Tactic
import SubdiffusiveProcess.Paper.lem_layer_norms
import SubdiffusiveProcess.Paper.cor_14
import SubdiffusiveProcess.Paper.lem_strips
import SubdiffusiveProcess.Paper.in_efron_stein
import SubdiffusiveProcess.Paper.aux_lem_15_bblm
import SubdiffusiveProcess.Paper.aux_lem_15_layer_tail
import SubdiffusiveProcess.Paper.aux_lem_15_masked_response
import SubdiffusiveProcess.Paper.aux_lem_15_update_H_ae
import SubdiffusiveProcess.Paper.aux_lem_15_lp_assemble
import SubdiffusiveProcess.Paper.lem_localized_perturbation
import SubdiffusiveProcess.Paper.prop_growth
import SubdiffusiveProcess.Paper.response_convention
import SubdiffusiveProcess.Paper.in_common_scale_coupling
import SubdiffusiveProcess.Paper.lem_infrared
import SubdiffusiveProcess.Paper.aux_lem_15_masked_response_estimates
import SubdiffusiveProcess.CoarseGrainingVocab.NegativeBesovSupport
import Mathlib
import SubdiffusiveProcess.Main.CutoffPotential
import SubdiffusiveProcess.Probability.CopyLayerBlock
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.LocalEnergy
import SubdiffusiveProcess.Sobolev.PartitionEnergy
import SubdiffusiveProcess.Sobolev.PotentialCoefficient

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

noncomputable section
namespace Paper

section UniformFourTerm
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology Pointwise

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-! ## The response selector -/



def aux_lem_15_u_resp (S : ResponseSpace Q) (dir : Bool) (bd : weakSobolevGraph Q)
    (L : S.space →L[ℝ] ℝ) (a : PositiveCoefficient Q) : ℝ :=
  if dir then dirichletResponse S a bd else inverseResponse S a L



def aux_lem_15_u_grad (S : ResponseSpace Q) (dir : Bool) (bd : weakSobolevGraph Q)
    (L : S.space →L[ℝ] ℝ) (a : PositiveCoefficient Q) : HilbertGradient Q :=
  if dir then sobolevGradient (dirichletMinimizer S a bd).val
  else subspaceGradient S.space (responseSolution S a L)

/-- Both responses are the energy of their minimizer. -/
theorem aux_lem_15_u_resp_eq (S : ResponseSpace Q) (dir : Bool) (bd : weakSobolevGraph Q)
    (L : S.space →L[ℝ] ℝ) (a : PositiveCoefficient Q) :
    aux_lem_15_u_resp S dir bd L a =
      weightedGradientForm a.val (aux_lem_15_u_grad S dir bd L a)
        (aux_lem_15_u_grad S dir bd L a) := by
  cases dir
  · simp only [aux_lem_15_u_resp, aux_lem_15_u_grad, Bool.false_eq_true, ↓reduceIte,
      inverseResponse, responseForm, ContinuousLinearMap.bilinearComp_apply]
  · simp only [aux_lem_15_u_resp, aux_lem_15_u_grad, ↓reduceIte, dirichletResponse,
      sobolevCoefficientForm, ContinuousLinearMap.bilinearComp_apply]

theorem aux_lem_15_u_resp_nonneg (S : ResponseSpace Q) (dir : Bool) (bd : weakSobolevGraph Q)
    (L : S.space →L[ℝ] ℝ) (a : PositiveCoefficient Q) :
    0 ≤ aux_lem_15_u_resp S dir bd L a := by
  cases dir
  · exact inverseResponse_nonneg S a L
  · exact dirichletResponse_nonneg S a bd

/-- `cor_14`, first two estimates, for the selected response: a bounded potential
perturbation `g` supported in `B` moves the minimizer by at most `s²e^{3s}Γ(B)` in
energy and the response by at most `2se^{4s}Γ(B)` (paper eq. (mfd-14)). -/
theorem aux_lem_15_u_perturb (S : ResponseSpace Q) (dir : Bool) (bd : weakSobolevGraph Q)
    (L : S.space →L[ℝ] ℝ)
    (h g : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d))))
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
    (hsupp : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), x ∉ B → g x = 0) :
    weightedGradientForm (expPotentialCoefficient (h + g)).val
        (aux_lem_15_u_grad S dir bd L (expPotentialCoefficient (h + g)) -
          aux_lem_15_u_grad S dir bd L (expPotentialCoefficient h))
        (aux_lem_15_u_grad S dir bd L (expPotentialCoefficient (h + g)) -
          aux_lem_15_u_grad S dir bd L (expPotentialCoefficient h)) ≤
      ‖g‖ ^ 2 * Real.exp (3 * ‖g‖) *
        localGradientEnergy (expPotentialCoefficient h) hB
          (aux_lem_15_u_grad S dir bd L (expPotentialCoefficient h)) ∧
    |aux_lem_15_u_resp S dir bd L (expPotentialCoefficient (h + g)) -
        aux_lem_15_u_resp S dir bd L (expPotentialCoefficient h)| ≤
      2 * ‖g‖ * Real.exp (4 * ‖g‖) *
        localGradientEnergy (expPotentialCoefficient h) hB
          (aux_lem_15_u_grad S dir bd L (expPotentialCoefficient h)) := by
  have hc := (cor_14.1 d Q S h g B hB hsupp L bd)
  dsimp only at hc
  obtain ⟨⟨hi1, _, hi3⟩, ⟨hd1, _, hd3⟩, _, _⟩ := hc
  cases dir
  · simp only [aux_lem_15_u_resp, aux_lem_15_u_grad, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, hi3⟩
    have he : responseForm S (expPotentialCoefficient (h + g))
        (responseSolution S (expPotentialCoefficient (h + g)) L -
          responseSolution S (expPotentialCoefficient h) L)
        (responseSolution S (expPotentialCoefficient (h + g)) L -
          responseSolution S (expPotentialCoefficient h) L) =
        weightedGradientForm (expPotentialCoefficient (h + g)).val
          (subspaceGradient S.space (responseSolution S (expPotentialCoefficient (h + g)) L) -
            subspaceGradient S.space (responseSolution S (expPotentialCoefficient h) L))
          (subspaceGradient S.space (responseSolution S (expPotentialCoefficient (h + g)) L) -
            subspaceGradient S.space (responseSolution S (expPotentialCoefficient h) L)) := by
      rw [← map_sub]; rfl
    rw [← he]
    exact hi1
  · simp only [aux_lem_15_u_resp, aux_lem_15_u_grad, ↓reduceIte]
    refine ⟨?_, hd3⟩
    have he : sobolevCoefficientForm (expPotentialCoefficient (h + g))
        ((dirichletMinimizer S (expPotentialCoefficient (h + g)) bd).val -
          (dirichletMinimizer S (expPotentialCoefficient h) bd).val)
        ((dirichletMinimizer S (expPotentialCoefficient (h + g)) bd).val -
          (dirichletMinimizer S (expPotentialCoefficient h) bd).val) =
        weightedGradientForm (expPotentialCoefficient (h + g)).val
          (sobolevGradient (dirichletMinimizer S (expPotentialCoefficient (h + g)) bd).val -
            sobolevGradient (dirichletMinimizer S (expPotentialCoefficient h) bd).val)
          (sobolevGradient (dirichletMinimizer S (expPotentialCoefficient (h + g)) bd).val -
            sobolevGradient (dirichletMinimizer S (expPotentialCoefficient h) bd).val) := by
      rw [← map_sub]; rfl
    rw [← he]
    exact hd1

/-- `cor_14`, multiplicative comparison (paper eq. (mfd-mult)) for the selected response. -/
theorem aux_lem_15_u_mult (S : ResponseSpace Q) (dir : Bool) (bd : weakSobolevGraph Q)
    (L : S.space →L[ℝ] ℝ) (p q : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d)))) :
    Real.exp (-‖p - q‖) * aux_lem_15_u_resp S dir bd L (expPotentialCoefficient q) ≤
        aux_lem_15_u_resp S dir bd L (expPotentialCoefficient p) ∧
      aux_lem_15_u_resp S dir bd L (expPotentialCoefficient p) ≤
        Real.exp ‖p - q‖ * aux_lem_15_u_resp S dir bd L (expPotentialCoefficient q) := by
  have hc := (cor_14.1 d Q S 0 0 Set.univ MeasurableSet.univ
    (Filter.Eventually.of_forall fun x hx => absurd (Set.mem_univ x) hx) L bd)
  dsimp only at hc
  obtain ⟨_, _, hinv, hdir⟩ := hc
  cases dir
  · simpa only [aux_lem_15_u_resp, Bool.false_eq_true, ↓reduceIte] using hinv p q
  · simpa only [aux_lem_15_u_resp, ↓reduceIte] using hdir p q

/-- The two-sided consequence `|R(p) - R(q)| ≤ (e^{‖p-q‖} - 1) R(q)`. -/
theorem aux_lem_15_u_resp_sub_le (S : ResponseSpace Q) (dir : Bool) (bd : weakSobolevGraph Q)
    (L : S.space →L[ℝ] ℝ) (p q : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d)))) :
    |aux_lem_15_u_resp S dir bd L (expPotentialCoefficient p) -
        aux_lem_15_u_resp S dir bd L (expPotentialCoefficient q)| ≤
      (Real.exp ‖p - q‖ - 1) * aux_lem_15_u_resp S dir bd L (expPotentialCoefficient q) := by
  obtain ⟨hlo, hhi⟩ := aux_lem_15_u_mult S dir bd L p q
  have hR := aux_lem_15_u_resp_nonneg S dir bd L (expPotentialCoefficient q)
  have hx : 0 ≤ ‖p - q‖ := norm_nonneg _
  have hkey : 1 - Real.exp (-‖p - q‖) ≤ Real.exp ‖p - q‖ - 1 := by
    have h1 := Real.add_one_le_exp ‖p - q‖
    have h2 : Real.exp (-‖p - q‖) * Real.exp ‖p - q‖ = 1 := by
      rw [← Real.exp_add]; simp
    have h3 : 0 < Real.exp (-‖p - q‖) := Real.exp_pos _
    nlinarith [Real.exp_pos ‖p - q‖]
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hkey hR]
  · nlinarith

/-- The selected response is a continuous function of the bounded potential. -/
theorem aux_lem_15_u_resp_continuous (S : ResponseSpace Q) (dir : Bool)
    (bd : weakSobolevGraph Q) (L : S.space →L[ℝ] ℝ) :
    Continuous (fun h : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d))) =>
      aux_lem_15_u_resp S dir bd L (expPotentialCoefficient h)) := by
  rw [continuous_iff_continuousAt]
  intro q
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hcont : Continuous (fun p : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d))) =>
      (Real.exp ‖p - q‖ - 1) * aux_lem_15_u_resp S dir bd L (expPotentialCoefficient q)) := by
    fun_prop
  have hlim := hcont.tendsto q
  simp only [sub_self, norm_zero, Real.exp_zero, zero_mul] at hlim
  refine squeeze_zero (fun p => dist_nonneg) (fun p => ?_) hlim
  rw [Real.dist_eq]
  exact aux_lem_15_u_resp_sub_le S dir bd L p q

/-! ## The energy measure of a gradient -/

/-- The energy density `a Σ_k g_k²` on `Q`. -/
def aux_lem_15_u_density (a : PositiveCoefficient Q) (g : HilbertGradient Q) :
    SpatialCoordinates d → ℝ :=
  fun x => ∑ i : Fin d, a.val x * (g i x * g i x)

theorem aux_lem_15_u_density_integrable (a : PositiveCoefficient Q) (g : HilbertGradient Q) :
    Integrable (aux_lem_15_u_density a g) (volume.restrict (Q : Set (SpatialCoordinates d))) :=
  integrable_finset_sum _ fun i _ => integrable_weighted_coordinates a.val g g i

theorem aux_lem_15_u_density_nonneg (a : PositiveCoefficient Q) (g : HilbertGradient Q) :
    0 ≤ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] aux_lem_15_u_density a g := by
  filter_upwards [positiveCoefficient_ae_nonneg a] with x hx
  exact Finset.sum_nonneg fun i _ => mul_nonneg hx (mul_self_nonneg _)

/-- The energy measure `Γ_a(g) = a|g|² dx` on `Q`. -/
def aux_lem_15_u_energyMeasure (a : PositiveCoefficient Q) (g : HilbertGradient Q) :
    Measure (SpatialCoordinates d) :=
  (volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
    (fun x => ENNReal.ofReal (aux_lem_15_u_density a g x))

theorem aux_lem_15_u_localEnergy_eq (a : PositiveCoefficient Q) (g : HilbertGradient Q)
    {A : Set (SpatialCoordinates d)} (hA : MeasurableSet A) :
    localGradientEnergy a hA g =
      ∫ x in A, aux_lem_15_u_density a g x ∂(volume.restrict (Q : Set (SpatialCoordinates d))) := by
  rw [localGradientEnergy_eq_integral]
  simp only [aux_lem_15_u_density]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards with x
    ring
  · intro i _
    exact (integrable_weighted_coordinates a.val g g i).integrableOn

theorem aux_lem_15_u_energyMeasure_apply (a : PositiveCoefficient Q) (g : HilbertGradient Q)
    {A : Set (SpatialCoordinates d)} (hA : MeasurableSet A) :
    aux_lem_15_u_energyMeasure a g A = ENNReal.ofReal (localGradientEnergy a hA g) := by
  rw [aux_lem_15_u_energyMeasure, withDensity_apply _ hA, aux_lem_15_u_localEnergy_eq a g hA,
    ofReal_integral_eq_lintegral_ofReal]
  · exact (aux_lem_15_u_density_integrable a g).integrableOn
  · exact ae_restrict_of_ae (aux_lem_15_u_density_nonneg a g)

theorem aux_lem_15_u_localEnergy_univ (a : PositiveCoefficient Q) (g : HilbertGradient Q) :
    localGradientEnergy a MeasurableSet.univ g = weightedGradientForm a.val g g := by
  rw [localGradientEnergy_eq_integral, weightedGradientForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards with x
  ring

instance aux_lem_15_u_energyMeasure_finite (a : PositiveCoefficient Q) (g : HilbertGradient Q) :
    IsFiniteMeasure (aux_lem_15_u_energyMeasure a g) :=
  isFiniteMeasure_withDensity_ofReal (aux_lem_15_u_density_integrable a g).hasFiniteIntegral

theorem aux_lem_15_u_energyMeasure_univ (a : PositiveCoefficient Q) (g : HilbertGradient Q) :
    aux_lem_15_u_energyMeasure a g Set.univ =
      ENNReal.ofReal (weightedGradientForm a.val g g) := by
  rw [aux_lem_15_u_energyMeasure_apply a g MeasurableSet.univ, aux_lem_15_u_localEnergy_univ]

/-- A finite disjoint family of measurable cores carries at most the total energy. -/
theorem aux_lem_15_u_sum_local_le {ι : Type*} (s : Finset ι) (C : ι → Set (SpatialCoordinates d))
    (hC : ∀ i, MeasurableSet (C i)) (hdisj : Set.PairwiseDisjoint (↑s) C)
    (a : PositiveCoefficient Q) (g : HilbertGradient Q) :
    ∑ i ∈ s, localGradientEnergy a (hC i) g ≤ weightedGradientForm a.val g g := by
  have hnn : ∀ i ∈ s, 0 ≤ localGradientEnergy a (hC i) g :=
    fun i _ => localGradientEnergy_nonneg a (hC i) g
  have htot : 0 ≤ weightedGradientForm a.val g g := by
    rw [← aux_lem_15_u_localEnergy_univ]; exact localGradientEnergy_nonneg _ _ _
  rw [← ENNReal.ofReal_le_ofReal_iff htot, ENNReal.ofReal_sum_of_nonneg hnn]
  calc ∑ i ∈ s, ENNReal.ofReal (localGradientEnergy a (hC i) g)
      = ∑ i ∈ s, aux_lem_15_u_energyMeasure a g (C i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [aux_lem_15_u_energyMeasure_apply a g (hC i)]
    _ = aux_lem_15_u_energyMeasure a g (⋃ i ∈ s, C i) :=
        (measure_biUnion_finset hdisj (fun i _ => hC i)).symm
    _ ≤ aux_lem_15_u_energyMeasure a g Set.univ := measure_mono (Set.subset_univ _)
    _ = ENNReal.ofReal (weightedGradientForm a.val g g) := aux_lem_15_u_energyMeasure_univ a g

/-- Local energy is monotone in the set. -/
theorem aux_lem_15_u_localEnergy_mono (a : PositiveCoefficient Q) (g : HilbertGradient Q)
    {A B : Set (SpatialCoordinates d)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) : localGradientEnergy a hA g ≤ localGradientEnergy a hB g := by
  have h1 := aux_lem_15_u_energyMeasure_apply a g hA
  have h2 := aux_lem_15_u_energyMeasure_apply a g hB
  have hm : aux_lem_15_u_energyMeasure a g A ≤ aux_lem_15_u_energyMeasure a g B :=
    measure_mono hAB
  rw [h1, h2] at hm
  exact (ENNReal.ofReal_le_ofReal_iff (localGradientEnergy_nonneg a hB g)).1 hm

/-- Local energy only sees the part of the set inside `Q`. -/
theorem aux_lem_15_u_energyMeasure_inter (a : PositiveCoefficient Q) (g : HilbertGradient Q)
    (A : Set (SpatialCoordinates d)) :
    aux_lem_15_u_energyMeasure a g (A ∩ (Q : Set (SpatialCoordinates d))) =
      aux_lem_15_u_energyMeasure a g A := by
  have hQ : MeasurableSet (Q : Set (SpatialCoordinates d)) := Q.isOpen.measurableSet
  have hac : aux_lem_15_u_energyMeasure a g ≪ volume.restrict (Q : Set (SpatialCoordinates d)) :=
    withDensity_absolutelyContinuous _ _
  have hnull : aux_lem_15_u_energyMeasure a g (Q : Set (SpatialCoordinates d))ᶜ = 0 :=
    hac (by rw [Measure.restrict_apply hQ.compl]; simp)
  exact measure_inter_conull hnull

/-! ## The `L∞(Q)` embedding of continuous fields cut off to a set -/


theorem aux_lem_15_u_emb_bound (K : Set (SpatialCoordinates d)) (hK : IsCompact K) (hQK : (Q : Set (SpatialCoordinates d)) ⊆ K)
    (A : Set (SpatialCoordinates d)) (f : C(SpatialCoordinates d, ℝ)) :
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      ‖A.indicator f x‖ ≤ ‖f.restrict K‖ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  filter_upwards [ae_restrict_mem Q.isOpen.measurableSet] with x hx
  calc ‖A.indicator f x‖ ≤ ‖f x‖ := by
        by_cases hA : x ∈ A
        · rw [Set.indicator_of_mem hA]
        · rw [Set.indicator_of_notMem hA, norm_zero]; exact norm_nonneg _
    _ = ‖f.restrict K ⟨x, hQK hx⟩‖ := rfl
    _ ≤ ‖f.restrict K‖ := ContinuousMap.norm_coe_le_norm _ _

theorem aux_lem_15_u_emb_memLp (K : Set (SpatialCoordinates d)) (hK : IsCompact K) (hQK : (Q : Set (SpatialCoordinates d)) ⊆ K)
    (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A) (f : C(SpatialCoordinates d, ℝ)) :
    MemLp (A.indicator f) ∞ (volume.restrict (Q : Set (SpatialCoordinates d))) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact memLp_top_of_bound ((f.continuous.measurable.indicator hA).aestronglyMeasurable)
    ‖f.restrict K‖ (aux_lem_15_u_emb_bound K hK hQK A f)

/-- The bounded potential `1_A f` on `Q`. -/
def aux_lem_15_u_emb (K : Set (SpatialCoordinates d)) (hK : IsCompact K) (hQK : (Q : Set (SpatialCoordinates d)) ⊆ K)
    (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A) (f : C(SpatialCoordinates d, ℝ)) :
    Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d))) :=
  (aux_lem_15_u_emb_memLp K hK hQK A hA f).toLp _

theorem aux_lem_15_u_emb_coeFn (K : Set (SpatialCoordinates d)) (hK : IsCompact K) (hQK : (Q : Set (SpatialCoordinates d)) ⊆ K)
    (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A) (f : C(SpatialCoordinates d, ℝ)) :
    (aux_lem_15_u_emb K hK hQK A hA f : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] A.indicator f :=
  (aux_lem_15_u_emb_memLp K hK hQK A hA f).coeFn_toLp

theorem aux_lem_15_u_emb_norm_le (K : Set (SpatialCoordinates d)) (hK : IsCompact K) (hQK : (Q : Set (SpatialCoordinates d)) ⊆ K)
    (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A) (f : C(SpatialCoordinates d, ℝ)) :
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ‖aux_lem_15_u_emb K hK hQK A hA f‖ ≤ ‖f.restrict K‖ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hQK).trans_lt hK.measure_lt_top⟩
  have hb := aux_lem_15_u_emb_bound K hK hQK A f
  have h := Lp.norm_le_of_ae_bound (norm_nonneg (f.restrict K))
    (f := aux_lem_15_u_emb K hK hQK A hA f) (by
      filter_upwards [hb, aux_lem_15_u_emb_coeFn K hK hQK A hA f] with x hx he
      rw [he]; exact hx)
  simpa using h

theorem aux_lem_15_u_emb_sub (K : Set (SpatialCoordinates d)) (hK : IsCompact K) (hQK : (Q : Set (SpatialCoordinates d)) ⊆ K)
    (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A) (f g : C(SpatialCoordinates d, ℝ)) :
    aux_lem_15_u_emb K hK hQK A hA (f - g) =
      aux_lem_15_u_emb K hK hQK A hA f - aux_lem_15_u_emb K hK hQK A hA g := by
  apply Lp.ext
  filter_upwards [aux_lem_15_u_emb_coeFn K hK hQK A hA (f - g),
    aux_lem_15_u_emb_coeFn K hK hQK A hA f, aux_lem_15_u_emb_coeFn K hK hQK A hA g,
    Lp.coeFn_sub (aux_lem_15_u_emb K hK hQK A hA f) (aux_lem_15_u_emb K hK hQK A hA g)]
    with x h1 h2 h3 h4
  rw [h1, h4, Pi.sub_apply, h2, h3]
  by_cases hx : x ∈ A
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

theorem aux_lem_15_u_emb_add (K : Set (SpatialCoordinates d)) (hK : IsCompact K) (hQK : (Q : Set (SpatialCoordinates d)) ⊆ K)
    (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A) (f g : C(SpatialCoordinates d, ℝ)) :
    aux_lem_15_u_emb K hK hQK A hA (f + g) =
      aux_lem_15_u_emb K hK hQK A hA f + aux_lem_15_u_emb K hK hQK A hA g := by
  have h := aux_lem_15_u_emb_sub K hK hQK A hA (f + g) g
  rw [add_sub_cancel_right] at h
  rw [h, sub_add_cancel]

/-- The embedding is continuous for the compact-open topology. -/
theorem aux_lem_15_u_emb_continuous (K : Set (SpatialCoordinates d)) (hK : IsCompact K) (hQK : (Q : Set (SpatialCoordinates d)) ⊆ K)
    (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A) :
    Continuous (aux_lem_15_u_emb K hK hQK A hA) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [continuous_iff_continuousAt]
  intro f0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hr : Tendsto (fun f : C(SpatialCoordinates d, ℝ) => ‖f.restrict K - f0.restrict K‖)
      (𝓝 f0) (𝓝 0) := by
    have := ((ContinuousMap.continuous_restrict K).tendsto f0)
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    exact this
  refine squeeze_zero (fun f => norm_nonneg _) (fun f => ?_) hr
  rw [← aux_lem_15_u_emb_sub]
  exact (aux_lem_15_u_emb_norm_le K hK hQK A hA (f - f0)).trans_eq (by rfl)


variable {d : ℕ}

/-- Open core of the grid box `idx` (shrunk by `w`). -/
def aux_lem_15_u_core (a : SpatialCoordinates d) (ell w : ℝ) (idx : Fin d → ℤ) :
    Set (SpatialCoordinates d) :=
  {x | ∀ c, a c + (idx c : ℝ) * ell + w < x c ∧ x c < a c + ((idx c : ℝ) + 1) * ell - w}

/-- Closed clamping box (shrunk by `w/2`). -/
def aux_lem_15_u_kbox (a : SpatialCoordinates d) (ell w : ℝ) (idx : Fin d → ℤ) :
    Set (SpatialCoordinates d) :=
  {x | ∀ c, a c + (idx c : ℝ) * ell + w / 2 ≤ x c ∧ x c ≤ a c + ((idx c : ℝ) + 1) * ell - w / 2}

/-- Open observation box (shrunk by `w/4`). -/
def aux_lem_15_u_ubox (a : SpatialCoordinates d) (ell w : ℝ) (idx : Fin d → ℤ) :
    Set (SpatialCoordinates d) :=
  {x | ∀ c, a c + (idx c : ℝ) * ell + w / 4 < x c ∧ x c < a c + ((idx c : ℝ) + 1) * ell - w / 4}

/-- Points within `w` of a grid hyperplane (the strips of `lem_strips`, before
intersecting with the cube). -/
def aux_lem_15_u_stripSet (a : SpatialCoordinates d) (ell w : ℝ) : Set (SpatialCoordinates d) :=
  {x | ∃ i : Fin d, ∃ j : ℤ, |x i - (a i + (j : ℝ) * ell)| ≤ w}

/-- Coordinatewise clamp onto the closed box. -/
def aux_lem_15_u_clamp (a : SpatialCoordinates d) (ell w : ℝ) (idx : Fin d → ℤ)
    (x : SpatialCoordinates d) : SpatialCoordinates d :=
  fun c => max (a c + (idx c : ℝ) * ell + w / 2) (min (a c + ((idx c : ℝ) + 1) * ell - w / 2) (x c))

theorem aux_lem_15_u_clamp_continuous (a : SpatialCoordinates d) (ell w : ℝ)
    (idx : Fin d → ℤ) : Continuous (aux_lem_15_u_clamp a ell w idx) := by
  unfold aux_lem_15_u_clamp
  fun_prop

theorem aux_lem_15_u_core_isOpen (a : SpatialCoordinates d) (ell w : ℝ) (idx : Fin d → ℤ) :
    IsOpen (aux_lem_15_u_core a ell w idx) := by
  have : aux_lem_15_u_core a ell w idx =
      ⋂ c, ({x : SpatialCoordinates d | a c + (idx c : ℝ) * ell + w < x c} ∩
        {x | x c < a c + ((idx c : ℝ) + 1) * ell - w}) := by
    ext x; simp [aux_lem_15_u_core]
  rw [this]
  exact isOpen_iInter_of_finite fun c =>
    (isOpen_lt continuous_const (continuous_apply c)).inter
      (isOpen_lt (continuous_apply c) continuous_const)

theorem aux_lem_15_u_ubox_isOpen (a : SpatialCoordinates d) (ell w : ℝ) (idx : Fin d → ℤ) :
    IsOpen (aux_lem_15_u_ubox a ell w idx) := by
  have : aux_lem_15_u_ubox a ell w idx =
      ⋂ c, ({x : SpatialCoordinates d | a c + (idx c : ℝ) * ell + w / 4 < x c} ∩
        {x | x c < a c + ((idx c : ℝ) + 1) * ell - w / 4}) := by
    ext x; simp [aux_lem_15_u_ubox]
  rw [this]
  exact isOpen_iInter_of_finite fun c =>
    (isOpen_lt continuous_const (continuous_apply c)).inter
      (isOpen_lt (continuous_apply c) continuous_const)

theorem aux_lem_15_u_stripSet_measurable (a : SpatialCoordinates d) (ell w : ℝ) :
    MeasurableSet (aux_lem_15_u_stripSet a ell w) := by
  have : aux_lem_15_u_stripSet a ell w =
      ⋃ i : Fin d, ⋃ j : ℤ, {x : SpatialCoordinates d | |x i - (a i + (j : ℝ) * ell)| ≤ w} := by
    ext x; simp [aux_lem_15_u_stripSet]
  rw [this]
  refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j => ?_
  exact measurableSet_le (by fun_prop) measurable_const

theorem aux_lem_15_u_core_subset_kbox (a : SpatialCoordinates d) {ell w : ℝ} (hw : 0 ≤ w)
    (idx : Fin d → ℤ) : aux_lem_15_u_core a ell w idx ⊆ aux_lem_15_u_kbox a ell w idx := by
  intro x hx c
  obtain ⟨h1, h2⟩ := hx c
  constructor <;> linarith

theorem aux_lem_15_u_kbox_subset_ubox (a : SpatialCoordinates d) {ell w : ℝ} (hw : 0 < w)
    (idx : Fin d → ℤ) : aux_lem_15_u_kbox a ell w idx ⊆ aux_lem_15_u_ubox a ell w idx := by
  intro x hx c
  obtain ⟨h1, h2⟩ := hx c
  constructor <;> linarith

/-- Cores avoid the strips. -/
theorem aux_lem_15_u_core_not_strip (a : SpatialCoordinates d) {ell w : ℝ} (hell : 0 ≤ ell)
    (idx : Fin d → ℤ) {x : SpatialCoordinates d} (hx : x ∈ aux_lem_15_u_core a ell w idx) :
    x ∉ aux_lem_15_u_stripSet a ell w := by
  rintro ⟨i, j, hj⟩
  obtain ⟨h1, h2⟩ := hx i
  rcases le_or_gt j (idx i) with hji | hji
  · have hjr : (j : ℝ) ≤ (idx i : ℝ) := by exact_mod_cast hji
    have : (j : ℝ) * ell ≤ (idx i : ℝ) * ell := mul_le_mul_of_nonneg_right hjr hell
    have habs := (abs_le.mp hj).2
    linarith
  · have hjr : (idx i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hji
    have : ((idx i : ℝ) + 1) * ell ≤ (j : ℝ) * ell := mul_le_mul_of_nonneg_right hjr hell
    have habs := (abs_le.mp hj).1
    linarith

/-- The floor index of a point. -/
def aux_lem_15_u_floorIdx (a : SpatialCoordinates d) (ell : ℝ) (x : SpatialCoordinates d) :
    Fin d → ℤ :=
  fun c => ⌊(x c - a c) / ell⌋

/-- Off the strips, a point lies in the core of its floor box. -/
theorem aux_lem_15_u_mem_core_of_not_strip (a : SpatialCoordinates d) {ell w : ℝ}
    (hell : 0 < ell) {x : SpatialCoordinates d} (hx : x ∉ aux_lem_15_u_stripSet a ell w) :
    x ∈ aux_lem_15_u_core a ell w (aux_lem_15_u_floorIdx a ell x) := by
  intro c
  have hlo := Int.floor_le ((x c - a c) / ell)
  have hhi := Int.lt_floor_add_one ((x c - a c) / ell)
  set k := ⌊(x c - a c) / ell⌋ with hk
  have h1 : (k : ℝ) * ell ≤ x c - a c := by
    have := mul_le_mul_of_nonneg_right hlo hell.le
    rwa [div_mul_cancel₀ _ hell.ne'] at this
  have h2 : x c - a c < ((k : ℝ) + 1) * ell := by
    have := mul_lt_mul_of_pos_right hhi hell
    rwa [div_mul_cancel₀ _ hell.ne'] at this
  have hne1 : ¬ |x c - (a c + (k : ℝ) * ell)| ≤ w := fun h => hx ⟨c, k, h⟩
  have hne2 : ¬ |x c - (a c + ((k + 1 : ℤ) : ℝ) * ell)| ≤ w := fun h => hx ⟨c, k + 1, h⟩
  push_neg at hne1 hne2
  push_cast at hne2
  simp only [aux_lem_15_u_floorIdx]
  rw [← hk]
  constructor
  · rw [abs_of_nonneg (by linarith)] at hne1
    linarith
  · rw [abs_of_neg (by linarith)] at hne2
    linarith

/-- Distinct observation boxes are separated by more than `w/2` in some coordinate. -/
theorem aux_lem_15_u_ubox_sep (a : SpatialCoordinates d) {ell w : ℝ} (hell : 0 ≤ ell)
    {idx idx' : Fin d → ℤ} (hne : idx ≠ idx') {x y : SpatialCoordinates d}
    (hx : x ∈ aux_lem_15_u_ubox a ell w idx) (hy : y ∈ aux_lem_15_u_ubox a ell w idx') :
    ∃ c, w / 2 < |x c - y c| := by
  obtain ⟨c, hc⟩ : ∃ c, idx c ≠ idx' c := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  refine ⟨c, ?_⟩
  obtain ⟨hx1, hx2⟩ := hx c
  obtain ⟨hy1, hy2⟩ := hy c
  rcases lt_or_gt_of_ne hc with hlt | hlt
  · have hr : (idx c : ℝ) + 1 ≤ (idx' c : ℝ) := by exact_mod_cast hlt
    have : ((idx c : ℝ) + 1) * ell ≤ (idx' c : ℝ) * ell := mul_le_mul_of_nonneg_right hr hell
    have hlt' : w / 2 < y c - x c := by linarith
    rw [abs_sub_comm]
    exact lt_of_lt_of_le hlt' (le_abs_self _)
  · have hr : (idx' c : ℝ) + 1 ≤ (idx c : ℝ) := by exact_mod_cast hlt
    have : ((idx' c : ℝ) + 1) * ell ≤ (idx c : ℝ) * ell := mul_le_mul_of_nonneg_right hr hell
    have hlt' : w / 2 < x c - y c := by linarith
    exact lt_of_lt_of_le hlt' (le_abs_self _)

/-- Distinct cores are disjoint. -/
theorem aux_lem_15_u_core_disjoint (a : SpatialCoordinates d) {ell w : ℝ} (hell : 0 ≤ ell)
    (hw : 0 < w) {idx idx' : Fin d → ℤ} (hne : idx ≠ idx') :
    Disjoint (aux_lem_15_u_core a ell w idx) (aux_lem_15_u_core a ell w idx') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 := aux_lem_15_u_kbox_subset_ubox a hw idx
    (aux_lem_15_u_core_subset_kbox a hw.le idx hx)
  have h2 := aux_lem_15_u_kbox_subset_ubox a hw idx'
    (aux_lem_15_u_core_subset_kbox a hw.le idx' hx')
  obtain ⟨c, hc⟩ := aux_lem_15_u_ubox_sep a hell hne h1 h2
  simp at hc
  linarith

theorem aux_lem_15_u_clamp_mem (a : SpatialCoordinates d) {ell w : ℝ} (hw : w ≤ ell)
    (idx : Fin d → ℤ) (x : SpatialCoordinates d) :
    aux_lem_15_u_clamp a ell w idx x ∈ aux_lem_15_u_kbox a ell w idx := by
  intro c
  simp only [aux_lem_15_u_clamp]
  constructor
  · exact le_max_left _ _
  · apply max_le _ (min_le_left _ _)
    linarith

theorem aux_lem_15_u_clamp_of_mem (a : SpatialCoordinates d) (ell w : ℝ)
    (idx : Fin d → ℤ) {x : SpatialCoordinates d} (hx : x ∈ aux_lem_15_u_kbox a ell w idx) :
    aux_lem_15_u_clamp a ell w idx x = x := by
  funext c
  obtain ⟨h1, h2⟩ := hx c
  simp only [aux_lem_15_u_clamp]
  rw [min_eq_right h2, max_eq_right h1]

/-- The finite index set of boxes meeting the cube `ball z (s/2)`. -/
def aux_lem_15_u_index (a z : SpatialCoordinates d) (s ell : ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun c => Finset.Icc ⌊(z c - s / 2 - a c) / ell⌋ ⌊(z c + s / 2 - a c) / ell⌋

theorem aux_lem_15_u_floorIdx_mem_index (a z : SpatialCoordinates d) {s ell : ℝ}
    (hell : 0 < ell) {x : SpatialCoordinates d} (hx : x ∈ Metric.ball z (s / 2)) :
    aux_lem_15_u_floorIdx a ell x ∈ aux_lem_15_u_index a z s ell := by
  rw [aux_lem_15_u_index, Fintype.mem_piFinset]
  intro c
  have hxc : |x c - z c| < s / 2 := by
    have h := (mem_ball_iff_norm.mp hx)
    exact lt_of_le_of_lt (norm_le_pi_norm (x - z) c) h
  rw [abs_lt] at hxc
  rw [Finset.mem_Icc]
  constructor
  · apply Int.floor_mono
    apply div_le_div_of_nonneg_right _ hell.le
    linarith
  · apply Int.floor_mono
    apply div_le_div_of_nonneg_right _ hell.le
    linarith

/-- Boxes of the index set lie in the enlarged closed cube `closedBall z (s/2 + 1)`. -/
theorem aux_lem_15_u_kbox_subset (a z : SpatialCoordinates d) {s ell w : ℝ}
    (hs0 : 0 ≤ s) (hell : 0 < ell) (hell1 : ell ≤ 1) (hw : 0 ≤ w) {idx : Fin d → ℤ}
    (hidx : idx ∈ aux_lem_15_u_index a z s ell) :
    aux_lem_15_u_kbox a ell w idx ⊆ Metric.closedBall z (s / 2 + 1) := by
  intro x hx
  rw [aux_lem_15_u_index, Fintype.mem_piFinset] at hidx
  rw [mem_closedBall_iff_norm]
  have hbd : ∀ c, |x c - z c| ≤ s / 2 + 1 := by
    intro c
    obtain ⟨h1, h2⟩ := hx c
    have hc := Finset.mem_Icc.mp (hidx c)
    have hlo1 : ((z c - s / 2 - a c) / ell) - 1 < (idx c : ℝ) := by
      have := Int.lt_floor_add_one ((z c - s / 2 - a c) / ell)
      have h' : (⌊(z c - s / 2 - a c) / ell⌋ : ℝ) ≤ (idx c : ℝ) := by exact_mod_cast hc.1
      linarith
    have hhi1 : (idx c : ℝ) ≤ (z c + s / 2 - a c) / ell := by
      have := Int.floor_le ((z c + s / 2 - a c) / ell)
      have h' : (idx c : ℝ) ≤ (⌊(z c + s / 2 - a c) / ell⌋ : ℝ) := by exact_mod_cast hc.2
      linarith
    have hlo2 : z c - s / 2 - a c - ell < (idx c : ℝ) * ell := by
      have := mul_lt_mul_of_pos_right hlo1 hell
      rw [sub_mul, div_mul_cancel₀ _ hell.ne', one_mul] at this
      exact this
    have hhi2 : (idx c : ℝ) * ell ≤ z c + s / 2 - a c := by
      have := mul_le_mul_of_nonneg_right hhi1 hell.le
      rwa [div_mul_cancel₀ _ hell.ne'] at this
    rw [abs_le]
    constructor <;> nlinarith
  have hnn : 0 ≤ s / 2 + 1 := by linarith
  exact (pi_norm_le_iff_of_nonneg hnn).2 fun c => by
    rw [Real.norm_eq_abs]; exact hbd c


/-! ## Measurability into `C(X, ℝ)` from evaluations (copied) -/

theorem aux_lem_15_u_mapsTo_iff
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    (K : Set X) (hK : IsCompact K) (D : Set X) (hDK : D ⊆ K) (hKD : K ⊆ closure D)
    (U : Set Y) (hU : IsOpen U) (hUc : (Uᶜ).Nonempty) (g : C(X, Y)) :
    Set.MapsTo g K U ↔ ∃ n : ℕ, ∀ x ∈ D, (1 : ℝ) / (n + 1) ≤ Metric.infDist (g x) Uᶜ := by
  have hclosed : IsClosed Uᶜ := hU.isClosed_compl
  have hcont : Continuous fun x => Metric.infDist (g x) Uᶜ :=
    (Metric.continuous_infDist_pt _).comp g.continuous
  constructor
  · intro hmaps
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · refine ⟨0, fun x hx => ?_⟩
      exact absurd (hDK hx) (by simp [hKe])
    obtain ⟨x0, hx0K, hmin⟩ := hK.exists_isMinOn hKne hcont.continuousOn
    have hpos : 0 < Metric.infDist (g x0) Uᶜ :=
      (hclosed.notMem_iff_infDist_pos hUc).mp (fun h => h (hmaps hx0K))
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    refine ⟨n, fun x hx => ?_⟩
    exact hn.le.trans (hmin (hDK hx))
  · rintro ⟨n, hn⟩ x hxK
    have hset : IsClosed {x | (1 : ℝ) / (n + 1) ≤ Metric.infDist (g x) Uᶜ} :=
      isClosed_le continuous_const hcont
    have hsub : closure D ⊆ {x | (1 : ℝ) / (n + 1) ≤ Metric.infDist (g x) Uᶜ} :=
      closure_minimal (fun y hy => hn y hy) hset
    have hx : (1 : ℝ) / (n + 1) ≤ Metric.infDist (g x) Uᶜ := hsub (hKD hxK)
    have hpos : 0 < Metric.infDist (g x) Uᶜ :=
      lt_of_lt_of_le (by positivity) hx
    have := (hclosed.notMem_iff_infDist_pos hUc).mpr hpos
    simpa using this

theorem aux_lem_15_u_measurable_of_eval
    {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
    [SecondCountableTopology C(X, ℝ)]
    [MeasurableSpace C(X, ℝ)] [BorelSpace C(X, ℝ)]
    (F : Ω → C(X, ℝ)) (hF : ∀ x, Measurable fun ω => F ω x) : Measurable F := by
  let S : Set (Set C(X, ℝ)) :=
    Set.image2 (fun K U => {f : C(X, ℝ) | Set.MapsTo f K U}) {K | IsCompact K} {t | IsOpen t}
  have hborel : (inferInstance : MeasurableSpace C(X, ℝ)) =
      MeasurableSpace.generateFrom S := by
    rw [BorelSpace.measurable_eq (α := C(X, ℝ))]
    exact borel_eq_generateFrom_of_subbasis ContinuousMap.compactOpen_eq
  have key : ∀ t ∈ S, MeasurableSet (F ⁻¹' t) := by
    rintro t ⟨K, hK, U, hU, rfl⟩
    change IsCompact K at hK
    change IsOpen U at hU
    rcases (Uᶜ).eq_empty_or_nonempty with hUe | hUc
    · have hUu : U = Set.univ := Set.compl_empty_iff.mp hUe
      subst hUu
      have : F ⁻¹' {f : C(X, ℝ) | Set.MapsTo f K Set.univ} = Set.univ := by
        ext ω; simp [Set.mapsTo_univ]
      rw [this]; exact MeasurableSet.univ
    obtain ⟨D, hDK, hDc, hKD⟩ := hK.isSeparable.exists_countable_dense_subset
    have heq : F ⁻¹' {f : C(X, ℝ) | Set.MapsTo f K U} =
        ⋃ n : ℕ, ⋂ x ∈ D, {ω | (1 : ℝ) / (n + 1) ≤ Metric.infDist (F ω x) Uᶜ} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
      exact aux_lem_15_u_mapsTo_iff K hK D hDK hKD U hU hUc (F ω)
    rw [heq]
    refine MeasurableSet.iUnion fun n => MeasurableSet.biInter hDc fun x _ => ?_
    exact measurableSet_le measurable_const
      ((Metric.continuous_infDist_pt _).measurable.comp (hF x))
  have h := @measurable_generateFrom Ω C(X, ℝ) _ S F key
  rw [← hborel] at h
  exact h

/-! ## Localized pieces and their independence -/

variable {d : ℕ}

/-- The clamped piece `η ∘ clamp_idx` of a field. -/
def aux_lem_15_u_localize (a : SpatialCoordinates d) (ell w : ℝ) (idx : Fin d → ℤ)
    (η : C(SpatialCoordinates d, ℝ)) : C(SpatialCoordinates d, ℝ) :=
  η.comp ⟨aux_lem_15_u_clamp a ell w idx, aux_lem_15_u_clamp_continuous a ell w idx⟩

theorem aux_lem_15_u_localize_continuous (a : SpatialCoordinates d) (ell w : ℝ)
    (idx : Fin d → ℤ) : Continuous (aux_lem_15_u_localize a ell w idx) :=
  (ContinuousMap.compRightContinuousMap ℝ
    ⟨aux_lem_15_u_clamp a ell w idx, aux_lem_15_u_clamp_continuous a ell w idx⟩).continuous

/-- The piece of the unit-scale potential seen by the scaled layer. -/
def aux_lem_15_u_piece (lam : ℝ) (a : SpatialCoordinates d) (ell w : ℝ) (idx : Fin d → ℤ)
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : C(SpatialCoordinates d, ℝ) :=
  g.1.1.comp ⟨fun x => lam • aux_lem_15_u_clamp a ell w idx x,
    continuous_const.smul (aux_lem_15_u_clamp_continuous a ell w idx)⟩

theorem aux_lem_15_u_piece_measurable [NeZero d] (lam : ℝ) (hlam : 0 < lam)
    (a : SpatialCoordinates d) {ell w : ℝ} (hw : 0 < w) (hwl : w ≤ ell) (idx : Fin d → ℤ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    @Measurable (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) C(SpatialCoordinates d, ℝ)
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma (lam • aux_lem_15_u_ubox a ell w idx)) _
      (aux_lem_15_u_piece lam a ell w idx) := by
  refine @aux_lem_15_u_measurable_of_eval (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
    (SpatialCoordinates d)
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma (lam • aux_lem_15_u_ubox a ell w idx))
    _ _ _ _ _ ?_
  intro x
  have hopen : IsOpen (lam • aux_lem_15_u_ubox a ell w idx) :=
    (aux_lem_15_u_ubox_isOpen a ell w idx).smul₀ hlam.ne'
  have hmem : lam • aux_lem_15_u_clamp a ell w idx x ∈ lam • aux_lem_15_u_ubox a ell w idx :=
    Set.smul_mem_smul_set (aux_lem_15_u_kbox_subset_ubox a hw idx
      (aux_lem_15_u_clamp_mem a hwl idx x))
  exact SubdiffusiveProcess.CoarseGrainingVocab.measurable_eval_potentialFieldLocalSigma_of_mem_isOpen hopen hmem

/-- Scaled observation boxes of distinct indices are separated at the (g1) range. -/
theorem aux_lem_15_u_rangeSeparated (lam : ℝ) (hlam : 0 < lam) (a : SpatialCoordinates d)
    {ell w : ℝ} (hell : 0 ≤ ell) (hsep : Real.sqrt (d : ℝ) ≤ lam * (w / 2))
    {idx idx' : Fin d → ℤ} (hne : idx ≠ idx') :
    SubdiffusiveProcess.CoarseGrainingVocab.PotentialRangeSeparated (lam • aux_lem_15_u_ubox a ell w idx)
      (lam • aux_lem_15_u_ubox a ell w idx') := by
  intro x' y' hx' hy'
  obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp hx'
  obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hy'
  obtain ⟨c, hc⟩ := aux_lem_15_u_ubox_sep a hell hne hx hy
  have h1 : ‖lam • x - lam • y‖ ≤ Homogenization.euclideanNorm (lam • x - lam • y) :=
    Homogenization.norm_le_euclideanNorm _
  have h2 : |(lam • x - lam • y) c| ≤ ‖lam • x - lam • y‖ := by
    have := norm_le_pi_norm (lam • x - lam • y) c
    rwa [Real.norm_eq_abs] at this
  have h3 : (lam • x - lam • y) c = lam * (x c - y c) := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [h3, abs_mul, abs_of_pos hlam] at h2
  have h4 : lam * (w / 2) ≤ lam * |x c - y c| := mul_le_mul_of_nonneg_left hc.le hlam.le
  linarith

private theorem aux_lem_15_u_measurableSet_biInter {ι : Type*} {U : ι → Set (SpatialCoordinates d)}
    {f : ι → Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)} {s : Finset ι}
    (hf : ∀ i ∈ s,
      @MeasurableSet (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma (U i)) (f i)) :
    @MeasurableSet (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma (⋃ i ∈ s, U i))
      (⋂ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hsubset_i : U i ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp only [Finset.mem_insert, Set.mem_iUnion]
        exact ⟨i, Or.inl rfl, hx⟩
      have hi_meas :
          @MeasurableSet (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma
              (⋃ j ∈ insert i s, U j)) (f i) :=
        (SubdiffusiveProcess.CoarseGrainingVocab.potentialFieldLocalSigma_mono hsubset_i) (f i)
          (hf i (by simp))
      have hsubset_s : (⋃ j ∈ s, U j) ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp only [Set.mem_iUnion] at hx
        obtain ⟨j, hj, hxj⟩ := hx
        simp only [Finset.mem_insert, Set.mem_iUnion]
        exact ⟨j, Or.inr hj, hxj⟩
      have hs_meas :
          @MeasurableSet (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma
              (⋃ j ∈ insert i s, U j)) (⋂ j ∈ s, f j) :=
        (SubdiffusiveProcess.CoarseGrainingVocab.potentialFieldLocalSigma_mono hsubset_s) (⋂ j ∈ s, f j)
          (ih fun j hj => hf j (by simp [hj]))
      simpa [Finset.set_biInter_insert, hi] using hi_meas.inter hs_meas

/-- (g1) upgrades to mutual independence of range-separated local σ-fields
(replay of `SubdiffusiveProcess.CoarseGrainingVocab.iIndep_potentialFieldLocalSigma_of_G1`). -/
theorem aux_lem_15_u_iIndep_localSigma {ι : Type*}
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (hG1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw) {U : ι → Set (SpatialCoordinates d)}
    (hU : ∀ i, MeasurableSet (U i))
    (hsep : Pairwise fun i j => SubdiffusiveProcess.CoarseGrainingVocab.PotentialRangeSeparated (U i) (U j)) :
    iIndep (fun i => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma (U i))
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure := by
  classical
  rw [iIndep_iff]
  intro s f hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hsep_union : SubdiffusiveProcess.CoarseGrainingVocab.PotentialRangeSeparated (U i) (⋃ j ∈ s, U j) := by
        intro x y hx hy
        simp only [Set.mem_iUnion] at hy
        obtain ⟨j, hj, hyj⟩ := hy
        exact hsep (by intro hij; exact hi (hij ▸ hj)) hx hyj
      have hs_meas :
          @MeasurableSet (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma (⋃ j ∈ s, U j))
            (⋂ j ∈ s, f j) :=
        aux_lem_15_u_measurableSet_biInter (U := U) (f := f) (s := s)
          fun j hj => hf j (by simp [hj])
      have h_inter :
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure
              (f i ∩ ⋂ j ∈ s, f j) =
            (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure (f i) *
              (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure (⋂ j ∈ s, f j) := by
        exact (Indep_iff
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma (U i))
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma (⋃ j ∈ s, U j))
            (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure).1
            (hG1.range_dependence (U i) (⋃ j ∈ s, U j)
              (hU i) (Finset.measurableSet_biUnion s fun j _ => hU j) hsep_union)
            (f i) (⋂ j ∈ s, f j) (hf i (by simp)) hs_meas
      calc
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure (⋂ j ∈ insert i s, f j) =
            (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure (f i ∩ ⋂ j ∈ s, f j) := by
              simp
        _ = (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure (f i) *
              (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure (⋂ j ∈ s, f j) := h_inter
        _ = (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure (f i) *
              ∏ j ∈ s, (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure (f j) := by
              rw [ih (fun j hj => hf j (by simp [hj]))]
        _ = ∏ j ∈ insert i s, (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure (f j) := by
              simp [Finset.prod_insert, hi]

/-- The pieces on distinct grid boxes are mutually independent under the root law. -/
theorem aux_lem_15_u_iIndepFun_pieces (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (hG1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw) (lam : ℝ) (hlam : 0 < lam)
    (a : SpatialCoordinates d) {ell w : ℝ} (hell : 0 ≤ ell) (hw : 0 < w) (hwl : w ≤ ell)
    (hsep : Real.sqrt (d : ℝ) ≤ lam * (w / 2)) {m : ℕ} (idx : Fin m → (Fin d → ℤ))
    (hinj : Function.Injective idx) :
    iIndepFun (fun k => aux_lem_15_u_piece lam a ell w (idx k))
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure := by
  haveI : NeZero d := ⟨by omega⟩
  have hind := aux_lem_15_u_iIndep_localSigma Praw hG1
    (U := fun k => lam • aux_lem_15_u_ubox a ell w (idx k))
    (fun k => ((aux_lem_15_u_ubox_isOpen a ell w (idx k)).smul₀ hlam.ne').measurableSet)
    (fun k k' hkk' => aux_lem_15_u_rangeSeparated lam hlam a hell hsep (hinj.ne hkk'))
  rw [iIndepFun_iff_iIndep, iIndep_iff]
  intro s f hf
  exact (iIndep_iff _ _).1 hind s
    (fun k hk => (Measurable.comap_le
      (aux_lem_15_u_piece_measurable lam hlam a hw hwl (idx k))) (f k) (hf k hk))

/-! ## The product law of the localized layer pieces -/

/-- The law of one layer of the common product law, as a pushforward of the root law. -/
theorem aux_lem_15_u_layer_law
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) (k : ℤ) :
    let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, C(SpatialCoordinates d, ℝ)) :=
      ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
    let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
      forget.continuous.measurable.aemeasurable
    let P := (commonScaleLaw d nu).toMeasure
    P.map (fun omega : BilateralField d => omega k) =
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure.map
        (fun g => layerScaling d k (forget g)) := by
  intro forget nu P
  ext A hA
  rw [Measure.map_apply (measurable_pi_apply k) hA,
    Measure.map_apply (show Measurable (fun g => layerScaling d k (forget g)) from
      ((layerScaling d k).continuous.comp forget.continuous).measurable) hA]
  exact aux_lem_15_layer_tail_transport Praw forget k A hA

theorem aux_lem_15_u_localize_layer (a : SpatialCoordinates d) (ell w : ℝ)
    (idx : Fin d → ℤ) (j : ℕ) (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
    aux_lem_15_u_localize a ell w idx (layerScaling d (-(j : ℤ)) g.1.1) =
      aux_lem_15_u_piece ((3 : ℝ) ^ (-(-(j : ℤ)))) a ell w idx g := by
  ext x
  rfl

/-- **Product law of the pieces** (paper line 1431): under the common product law,
the clamped pieces of layer `-j` on distinct boxes have the product law. -/
theorem aux_lem_15_u_key_law (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (hG1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw) (j : ℕ)
    (a : SpatialCoordinates d) {ell w : ℝ} (hell : 0 ≤ ell) (hw : 0 < w) (hwl : w ≤ ell)
    (hsep : Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (-(-(j : ℤ))) * (w / 2)) {m : ℕ}
    (idx : Fin m → (Fin d → ℤ)) (hinj : Function.Injective idx) :
    let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, C(SpatialCoordinates d, ℝ)) :=
      ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
    let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
      forget.continuous.measurable.aemeasurable
    let P := (commonScaleLaw d nu).toMeasure
    P.map (fun omega : BilateralField d => fun k : Fin m =>
        aux_lem_15_u_localize a ell w (idx k) (omega (-(j : ℤ)))) =
      Measure.pi (fun k : Fin m =>
        (P.map (fun omega : BilateralField d => omega (-(j : ℤ)))).map
          (aux_lem_15_u_localize a ell w (idx k))) := by
  intro forget nu P
  haveI : NeZero d := ⟨by omega⟩
  have hlam : (0 : ℝ) < (3 : ℝ) ^ (-(-(j : ℤ))) := zpow_pos (by norm_num) _
  have hlayer := aux_lem_15_u_layer_law Praw (-(j : ℤ))
  simp only at hlayer
  have hLmeas : Measurable (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
      layerScaling d (-(j : ℤ)) (forget g)) :=
    ((layerScaling d (-(j : ℤ))).continuous.comp forget.continuous).measurable
  have hTmeas : ∀ k, Measurable (aux_lem_15_u_localize a ell w (idx k)) :=
    fun k => (aux_lem_15_u_localize_continuous a ell w (idx k)).measurable
  have hvec : Measurable (fun η : C(SpatialCoordinates d, ℝ) => fun k : Fin m =>
      aux_lem_15_u_localize a ell w (idx k) η) :=
    measurable_pi_lambda _ hTmeas
  have hind := aux_lem_15_u_iIndepFun_pieces hd Praw hG1 _ hlam a hell hw hwl hsep idx hinj
  have hpi := (iIndepFun_iff_map_fun_eq_pi_map
    (fun k => (Measurable.mono (aux_lem_15_u_piece_measurable (d := d) _ hlam a hw hwl (idx k))
      (SubdiffusiveProcess.CoarseGrainingVocab.potentialFieldLocalSigma_le_borel _) le_rfl).aemeasurable)).1 hind
  have hcomp : ∀ k, (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
      aux_lem_15_u_piece ((3 : ℝ) ^ (-(-(j : ℤ)))) a ell w (idx k) g) =
      (aux_lem_15_u_localize a ell w (idx k)) ∘
        (fun g => layerScaling d (-(j : ℤ)) (forget g)) := by
    intro k; funext g
    exact (aux_lem_15_u_localize_layer a ell w (idx k) j g).symm
  calc P.map (fun omega : BilateralField d => fun k : Fin m =>
        aux_lem_15_u_localize a ell w (idx k) (omega (-(j : ℤ))))
      = (P.map (fun omega : BilateralField d => omega (-(j : ℤ)))).map
          (fun η k => aux_lem_15_u_localize a ell w (idx k) η) := by
        rw [Measure.map_map hvec (measurable_pi_apply _)]
        rfl
    _ = ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure.map
          (fun g => layerScaling d (-(j : ℤ)) (forget g))).map
          (fun η k => aux_lem_15_u_localize a ell w (idx k) η) := by rw [hlayer]
    _ = (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure.map
          (fun g k => aux_lem_15_u_piece ((3 : ℝ) ^ (-(-(j : ℤ)))) a ell w (idx k) g) := by
        rw [Measure.map_map hvec hLmeas]
        rfl
    _ = Measure.pi (fun k => (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure.map
          (fun g => aux_lem_15_u_piece ((3 : ℝ) ^ (-(-(j : ℤ)))) a ell w (idx k) g)) := hpi
    _ = Measure.pi (fun k : Fin m =>
        (P.map (fun omega : BilateralField d => omega (-(j : ℤ)))).map
          (aux_lem_15_u_localize a ell w (idx k))) := by
        congr 1
        funext k
        rw [hlayer, Measure.map_map (hTmeas k) hLmeas, hcomp k]

/-! ## Transfer between the diagonal and the product -/

/-- Replacing one coordinate of the common product law by the same coordinate of an
independent copy preserves the law. -/
theorem aux_lem_15_u_update_measurePreserving {I : Type*} [DecidableEq I] {X : Type*}
    [MeasurableSpace X] (μs : I → Measure X) [∀ i, IsProbabilityMeasure (μs i)] (k0 : I) :
    MeasurePreserving (fun p : (I → X) × (I → X) => Function.update p.1 k0 (p.2 k0))
      ((Measure.infinitePi μs).prod (Measure.infinitePi μs)) (Measure.infinitePi μs) := by
  classical
  have h := SubdiffusiveProcess.measurePreserving_copy_infinitePi_block
    (X := fun _ : I => X) μs ({k0} : Set I)
  convert h using 1
  funext p i
  by_cases hi : i = k0
  · subst hi; simp
  · simp [Function.update, hi]

/-- **Transfer lemma.**  For a function of (other data, pieces), the diagonal integral
equals the integral over independent pieces, as long as the "other data" is invariant
under replacing coordinate `k0`. -/
theorem aux_lem_15_u_transfer {I : Type*} [DecidableEq I] {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μs : I → Measure X) [∀ i, IsProbabilityMeasure (μs i)] (k0 : I)
    (base : (I → X) → Y) (hbase : Measurable base)
    (hinv : ∀ᵐ p ∂((Measure.infinitePi μs).prod (Measure.infinitePi μs)),
      base (Function.update p.1 k0 (p.2 k0)) = base p.1)
    (T : X → Z) (hT : Measurable T) (π : Measure Z)
    (hπ : (Measure.infinitePi μs).map (fun ω => T (ω k0)) = π)
    (ψ : Y × Z → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ ω, ψ (base ω, T (ω k0)) ∂(Measure.infinitePi μs) =
      ∫⁻ ω, ∫⁻ z, ψ (base ω, z) ∂π ∂(Measure.infinitePi μs) := by
  set P := Measure.infinitePi μs with hP
  have hU := aux_lem_15_u_update_measurePreserving μs k0
  have hF : Measurable (fun ω : I → X => ψ (base ω, T (ω k0))) :=
    hψ.comp (hbase.prodMk (hT.comp (measurable_pi_apply k0)))
  rw [← hU.lintegral_comp hF]
  have hae : (fun p : (I → X) × (I → X) =>
      ψ (base (Function.update p.1 k0 (p.2 k0)), T (Function.update p.1 k0 (p.2 k0) k0)))
      =ᵐ[P.prod P] fun p => ψ (base p.1, T (p.2 k0)) := by
    filter_upwards [hinv] with p hp
    rw [hp, Function.update_self]
  rw [lintegral_congr_ae hae]
  have hG : Measurable (fun p : (I → X) × (I → X) => ψ (base p.1, T (p.2 k0))) :=
    hψ.comp ((hbase.comp measurable_fst).prodMk
      (hT.comp ((measurable_pi_apply k0).comp measurable_snd)))
  rw [lintegral_prod _ hG.aemeasurable]
  apply lintegral_congr
  intro ω
  have hTk : Measurable (fun ω' : I → X => T (ω' k0)) := hT.comp (measurable_pi_apply k0)
  have hψω : Measurable (fun z : Z => ψ (base ω, z)) := hψ.comp measurable_prodMk_left
  rw [← hπ, lintegral_map hψω hTk]


/-- `aux_lem_15_layer_tail` with the tail constant fixed from the cube radius. -/
theorem aux_lem_15_u_layer_tail
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Q : Set (SpatialCoordinates d)) (hQ : IsCompact Q) (hQne : Q.Nonempty)
    (R : ℝ) (hR : 0 ≤ R) (hQR : ∀ x ∈ Q, ∀ i, |x i| ≤ R)
    (delta : ℝ) (hdelta : 0 < delta)
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (hG1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
    (hG2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw) :
    let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
        C(SpatialCoordinates d, ℝ)) :=
      ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
    let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
      forget.continuous.measurable.aemeasurable
    let P := (commonScaleLaw d nu).toMeasure
    let S : ℕ → BilateralField d → ℝ := fun j omega =>
      sSup ((fun x : SpatialCoordinates d => ‖omega (-(j : ℤ)) x‖) '' Q)
    let Cc : ℝ := max 1 ((4 * R + 5) ^ d)
    ∃ covers : ℕ → ℝ,
      (∀ j, 1 ≤ covers j) ∧
      (∀ j, covers j ≤ Cc * ((3 : ℝ) ^ (-(j : ℝ))) ^ (-(d : ℝ))) ∧
      (∀ j, AEStronglyMeasurable (S j) P) ∧
      (∀ j omega, 0 ≤ S j omega) ∧
      (∀ (j : ℕ) (s : ℝ), 0 ≤ s →
        P {omega | s < S j omega} ≤
          ENNReal.ofReal (2 * covers j * Real.exp (-(s ^ 2 / (Cc * delta ^ 2))))) := by
  classical
  intro forget nu P S Cc
  haveI hQc : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  haveI : Nonempty Q := hQne.to_subtype
  set M : ℕ → ℕ := fun j => ⌈2 * ((3 : ℝ) ^ j * R) + 1⌉₊ with hMdef
  set L : ℕ → Finset (Fin d → ℤ) := fun j =>
    Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(M j : ℤ)) (M j : ℤ)) with hLdef
  have hCc : (1 : ℝ) ≤ Cc := le_max_left _ _
  have hcardval : ∀ j, (L j).card = (2 * M j + 1) ^ d := by
    intro j
    rw [hLdef]
    exact aux_lem_15_layer_tail_card (M j)
  have hiSup : ∀ j omega, S j omega
      = ⨆ x : Q, ‖(omega (-(j : ℤ)) : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d)‖ := by
    intro j omega
    exact aux_lem_15_layer_tail_sSup_eq_iSup Q _
  refine ⟨fun j => ((L j).card : ℝ), ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    show (1 : ℝ) ≤ ((L j).card : ℝ)
    have h1 : 1 ≤ (L j).card := by
      rw [hcardval j]
      exact Nat.one_le_pow _ _ (by omega)
    exact_mod_cast h1
  · intro j
    show ((L j).card : ℝ) ≤ Cc * ((3 : ℝ) ^ (-(j : ℝ))) ^ (-(d : ℝ))
    rw [aux_lem_15_layer_tail_rpow]
    have hMlt : ((M j : ℝ)) < 2 * ((3 : ℝ) ^ j * R) + 2 := by
      have h := Nat.ceil_lt_add_one (a := 2 * ((3 : ℝ) ^ j * R) + 1) (by positivity)
      rw [hMdef]
      simpa using h.trans_le (by linarith)
    have hcast : ((L j).card : ℝ) = ((2 * M j + 1 : ℕ) : ℝ) ^ d := by
      rw [hcardval j]; push_cast; ring
    calc ((L j).card : ℝ) = ((2 * M j + 1 : ℕ) : ℝ) ^ d := hcast
      _ ≤ (4 * R + 5) ^ d * ((3 : ℝ) ^ j) ^ d :=
          aux_lem_15_layer_tail_growth R d j (M j) hMlt
      _ ≤ Cc * ((3 : ℝ) ^ j) ^ d :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · intro j
    have hfun : S j = (fun f : C(SpatialCoordinates d, ℝ) =>
        ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖) ∘
        (fun omega : BilateralField d => omega (-(j : ℤ))) := by
      funext omega
      exact hiSup j omega
    rw [hfun]
    exact (((aux_lem_15_layer_tail_continuous Q).measurable).comp
      (measurable_pi_apply _)).aestronglyMeasurable
  · intro j omega
    rw [hiSup j omega]
    exact aux_lem_15_layer_tail_iSup_nonneg Q _
  · intro j s hs
    show P {omega | s < S j omega} ≤
      ENNReal.ofReal (2 * ((L j).card : ℝ) * Real.exp (-(s ^ 2 / (Cc * delta ^ 2))))
    have hA : MeasurableSet {f : C(SpatialCoordinates d, ℝ) |
        s < ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖} :=
      (aux_lem_15_layer_tail_continuous Q).measurable measurableSet_Ioi
    have hset : {omega : BilateralField d | s < S j omega}
        = (fun omega : BilateralField d => omega (-(j : ℤ))) ⁻¹'
          {f : C(SpatialCoordinates d, ℝ) | s < ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖} := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      rw [hiSup j omega]
    rw [hset]
    have htrans := aux_lem_15_layer_tail_transport Praw forget (-(j : ℤ)) _ hA
    rw [show P = (commonScaleLaw d ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        forget.continuous.measurable.aemeasurable)).toMeasure from rfl, htrans]
    have hsubset : (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
          layerScaling d (-(j : ℤ)) (forget g)) ⁻¹'
          {f : C(SpatialCoordinates d, ℝ) | s < ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖}
        ⊆ ⋃ m ∈ L j, {g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d |
            s < SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
                (aux_lem_15_layer_tail_site m) g)} := by
      intro g hg
      have hg' : s < sSup ((fun x : SpatialCoordinates d =>
          ‖(layerScaling d (-(j : ℤ)) (forget g)) x‖) '' Q) := by
        rw [aux_lem_15_layer_tail_sSup_eq_iSup]
        exact hg
      obtain ⟨b, hb, hsb⟩ := exists_lt_of_lt_csSup (hQne.image _) hg'
      obtain ⟨x, hxQ, rfl⟩ := hb
      have hpow : ((3 : ℝ) ^ (-(-(j : ℤ)))) = (3 : ℝ) ^ (j : ℕ) := by
        rw [neg_neg, zpow_natCast]
      have hyv : (layerScaling d (-(j : ℤ)) (forget g)) x
          = (forget g) (((3 : ℝ) ^ (j : ℕ)) • x) := by
        show (forget g) (((3 : ℝ) ^ (-(-(j : ℤ)))) • x) = _
        rw [hpow]
      have hybound : ∀ i, |(((3 : ℝ) ^ (j : ℕ)) • x) i| ≤ (3 : ℝ) ^ j * R := by
        intro i
        have hxi : (((3 : ℝ) ^ (j : ℕ)) • x) i = (3 : ℝ) ^ j * x i := rfl
        rw [hxi, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ j)]
        exact mul_le_mul_of_nonneg_left (hQR x hxQ i) (by positivity)
      have hMle : 2 * ((3 : ℝ) ^ j * R) + 1 ≤ (M j : ℝ) := by
        rw [hMdef]
        exact Nat.le_ceil _
      obtain ⟨m, hm, hmem⟩ := aux_lem_15_layer_tail_cover ((3 : ℝ) ^ j * R) (M j) hMle
        (((3 : ℝ) ^ (j : ℕ)) • x) hybound
      refine Set.mem_biUnion (show m ∈ L j by rw [hLdef]; exact hm) ?_
      have hbound := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.abs_apply_le_g2Observable
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate (aux_lem_15_layer_tail_site m) g) hmem
      rw [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply, sub_add_cancel] at hbound
      show s < _
      refine lt_of_lt_of_le ?_ hbound
      simpa [hyv, Real.norm_eq_abs] using hsb
    calc (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure
          ((fun g => layerScaling d (-(j : ℤ)) (forget g)) ⁻¹'
            {f : C(SpatialCoordinates d, ℝ) | s < ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖})
        ≤ (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure
            (⋃ m ∈ L j, {g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d |
              s < SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
                  (aux_lem_15_layer_tail_site m) g)}) := measure_mono hsubset
      _ ≤ ∑ m ∈ L j, (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure
            {g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d |
              s < SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
                  (aux_lem_15_layer_tail_site m) g)} := measure_biUnion_finset_le _ _
      _ ≤ ∑ _m ∈ L j, ENNReal.ofReal (2 * Real.exp (-(s ^ 2 / delta ^ 2))) :=
          Finset.sum_le_sum (fun m _ =>
            aux_lem_15_layer_tail_translated_tail delta hdelta Praw hG1 hG2 _ s hs)
      _ = ((L j).card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-(s ^ 2 / delta ^ 2))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (2 * ((L j).card : ℝ) *
            Real.exp (-(s ^ 2 / (Cc * delta ^ 2)))) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hd2 : (0 : ℝ) < delta ^ 2 := by positivity
          have hle : delta ^ 2 ≤ Cc * delta ^ 2 := by nlinarith [hCc, hd2]
          have hdiv : s ^ 2 / (Cc * delta ^ 2) ≤ s ^ 2 / delta ^ 2 := by
            gcongr
          have hE : Real.exp (-(s ^ 2 / delta ^ 2))
              ≤ Real.exp (-(s ^ 2 / (Cc * delta ^ 2))) := by
            exact Real.exp_le_exp.mpr (by linarith)
          have hc : (0 : ℝ) ≤ ((L j).card : ℝ) := Nat.cast_nonneg _
          nlinarith [Real.exp_pos (-(s ^ 2 / delta ^ 2)),
            Real.exp_pos (-(s ^ 2 / (Cc * delta ^ 2)))]

/-- **Uniform layer-moment bank.**  For fixed `(p,k,λ,γ)` there is one constant for
all disorders `δ ∈ (0,1]`, all laws satisfying (g1),(g2) and all layers `j`. -/
theorem aux_lem_15_u_layer_moment
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Q : Set (SpatialCoordinates d)) (hQ : IsCompact Q) (hQne : Q.Nonempty)
    (R : ℝ) (hR : 0 ≤ R) (hQR : ∀ x ∈ Q, ∀ i, |x i| ≤ R)
    (p k lam gam : ℝ) (hp : 0 < p) (hk : 0 ≤ k) (hlam : 0 ≤ lam) (hgam : 0 < gam) :
    ∃ Cm : ℝ, 0 < Cm ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
      ∀ (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)),
        SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw →
        SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw →
        let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ)) :=
          ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
        let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
          forget.continuous.measurable.aemeasurable
        let P := (commonScaleLaw d nu).toMeasure
        ∀ j : ℕ,
          eLpNorm (fun omega : BilateralField d =>
              (sSup ((fun x : SpatialCoordinates d => ‖omega (-(j : ℤ)) x‖) '' Q)) ^ k *
                Real.exp (lam * sSup ((fun x : SpatialCoordinates d =>
                  ‖omega (-(j : ℤ)) x‖) '' Q)))
            (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (Cm * delta ^ k * ((3 : ℝ) ^ (-(j : ℝ))) ^ (-gam)) := by
  have hCc1 : (1 : ℝ) ≤ max 1 ((4 * R + 5) ^ d) := le_max_left _ _
  have hLN := lem_layer_norms d (by omega) (max 1 ((4 * R + 5) ^ d)) hCc1
  rcases hLN with ⟨C0, hC0, hLN⟩
  have hLN2 := hLN p hp
  rcases hLN2 with ⟨Cp, hCp, hLN2⟩
  have hLN3 := hLN2 k lam hk hlam
  rcases hLN3 with ⟨Cpk, hCpk, hLN3⟩
  have hLN4 := hLN3 gam hgam
  rcases hLN4 with ⟨Cpkg, hCpkg, hLN4⟩
  refine ⟨Cpkg, hCpkg, ?_⟩
  intro delta hdelta hdelta1 Praw hG1 hG2 forget nu P j
  have htail := aux_lem_15_u_layer_tail d Q hQ hQne R hR hQR delta hdelta Praw hG1 hG2
  simp only at htail
  rcases htail with ⟨covers, hcov1, hcov2, hSmeas, hSnn, hStail⟩
  have hres := hLN4 (BilateralField d) P delta hdelta hdelta1
    (fun j omega => sSup ((fun x : SpatialCoordinates d => ‖omega (-(j : ℤ)) x‖) '' Q))
    hSmeas hSnn covers hcov1 hcov2 hStail
  have hres2 := (hres.2 j)
  simp only at hres2
  exact hres2.1.trans (ENNReal.ofReal_le_ofReal hres2.2)

/-! ## Hölder and exponent helpers -/

theorem aux_lem_15_u_holder {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun x => f x * g x) (ENNReal.ofReal p) μ ≤
      eLpNorm f (ENNReal.ofReal (2 * p)) μ * eLpNorm g (ENNReal.ofReal (2 * p)) μ := by
  haveI : ENNReal.HolderTriple (ENNReal.ofReal (2 * p)) (ENNReal.ofReal (2 * p))
      (ENNReal.ofReal p) := ⟨by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_inv_of_pos hp,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    ring⟩
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := ENNReal.ofReal (2 * p))
    (q := ENNReal.ofReal (2 * p)) (r := ENNReal.ofReal p) hf hg (fun a b => a * b) 1
    (Filter.Eventually.of_forall fun x => by simp [norm_mul])
  simpa using h

theorem aux_lem_15_u_exponent_mono {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : AEStronglyMeasurable f μ) {p q : ℝ}
    (hpq : p ≤ q) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ eLpNorm f (ENNReal.ofReal q) μ :=
  eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq) hf


theorem aux_lem_15_u_eLpNorm_rpow {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {p : ℝ} (hp : 0 < p) (g : α → ℝ) :
    eLpNorm g (ENNReal.ofReal p) μ ^ p = ∫⁻ x, ‖g x‖ₑ ^ p ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by simpa using hp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, one_div, ENNReal.rpow_inv_rpow hp.ne']

theorem aux_lem_15_u_eLpNorm_eq_rpow {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {p : ℝ} (hp : 0 < p) (g : α → ℝ) :
    eLpNorm g (ENNReal.ofReal p) μ = (∫⁻ x, ‖g x‖ₑ ^ p ∂μ) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by simpa using hp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]

/-- Efron–Stein applied conditionally and transferred to the diagonal. -/
theorem aux_lem_15_u_es_diag {I : Type*} [DecidableEq I] {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μs : I → Measure X) [∀ i, IsProbabilityMeasure (μs i)] (k0 : I)
    (base : (I → X) → Y) (hbase : Measurable base)
    (hinv : ∀ᵐ q ∂((Measure.infinitePi μs).prod (Measure.infinitePi μs)),
      base (Function.update q.1 k0 (q.2 k0)) = base q.1)
    {m : ℕ} (μk : Fin m → Measure X) [∀ k, IsProbabilityMeasure (μk k)]
    (T : X → (Fin m → X)) (hT : Measurable T)
    (hπ : (Measure.infinitePi μs).map (fun ω => T (ω k0)) = Measure.pi μk)
    (Ψ : Y → (Fin m → X) → ℝ) (hΨ : Measurable (Function.uncurry Ψ))
    (p Cp : ℝ) (hp : 0 < p)
    (hES : ∀ F : (Fin m → X) → ℝ, AEStronglyMeasurable F (Measure.pi μk) →
      MemLp F (ENNReal.ofReal p) (Measure.pi μk) →
      eLpNorm (fun x => F x - ∫ y, F y ∂(Measure.pi μk)) (ENNReal.ofReal p) (Measure.pi μk) ≤
        ENNReal.ofReal Cp *
          eLpNorm (fun x => Real.sqrt
            (∑ i : Fin m, ∫ y : X, (F x - F (Function.update x i y)) ^ 2 ∂μk i))
            (ENNReal.ofReal p) (Measure.pi μk))
    (hmem : ∀ y, MemLp (Ψ y) (ENNReal.ofReal p) (Measure.pi μk)) :
    eLpNorm (fun ω => Ψ (base ω) (T (ω k0)) - ∫ v, Ψ (base ω) v ∂(Measure.pi μk))
        (ENNReal.ofReal p) (Measure.infinitePi μs) ≤
      ENNReal.ofReal Cp *
        eLpNorm (fun ω => Real.sqrt (∑ i : Fin m, ∫ y : X,
            (Ψ (base ω) (T (ω k0)) - Ψ (base ω) (Function.update (T (ω k0)) i y)) ^ 2 ∂μk i))
          (ENNReal.ofReal p) (Measure.infinitePi μs) := by
  set π := Measure.pi μk with hπdef
  set P := Measure.infinitePi μs with hPdef
  -- measurability of the conditional mean and of the variance proxy
  have hΨs : StronglyMeasurable (Function.uncurry Ψ) := hΨ.stronglyMeasurable
  have hG : Measurable (fun y => ∫ v, Ψ y v ∂π) :=
    (hΨs.integral_prod_right (ν := π)).measurable
  have hVin : ∀ i : Fin m, Measurable (fun q : (Y × (Fin m → X)) × X =>
      (Ψ q.1.1 q.1.2 - Ψ q.1.1 (Function.update q.1.2 i q.2)) ^ 2) := by
    intro i
    have h1 : Measurable (fun q : (Y × (Fin m → X)) × X => Ψ q.1.1 q.1.2) :=
      hΨ.comp measurable_fst
    have h2 : Measurable (fun q : (Y × (Fin m → X)) × X =>
        Ψ q.1.1 (Function.update q.1.2 i q.2)) := by
      have hu : Measurable (fun q : (Y × (Fin m → X)) × X =>
          (q.1.1, Function.update q.1.2 i q.2)) :=
        (measurable_fst.comp measurable_fst).prodMk
          (measurable_update'.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
      exact hΨ.comp hu
    exact (h1.sub h2).pow_const 2
  have hV : Measurable (fun yv : Y × (Fin m → X) => Real.sqrt (∑ i : Fin m, ∫ x : X,
      (Ψ yv.1 yv.2 - Ψ yv.1 (Function.update yv.2 i x)) ^ 2 ∂μk i)) := by
    refine Measurable.sqrt (Finset.measurable_sum _ fun i _ => ?_)
    exact ((hVin i).stronglyMeasurable.integral_prod_right' (ν := μk i)).measurable
  have hp' : (0 : ℝ) ≤ p := hp.le
  set ψ1 : Y × (Fin m → X) → ℝ≥0∞ := fun yv =>
    ‖Ψ yv.1 yv.2 - ∫ v, Ψ yv.1 v ∂π‖ₑ ^ p with hψ1
  set ψ2 : Y × (Fin m → X) → ℝ≥0∞ := fun yv =>
    ‖Real.sqrt (∑ i : Fin m, ∫ x : X,
      (Ψ yv.1 yv.2 - Ψ yv.1 (Function.update yv.2 i x)) ^ 2 ∂μk i)‖ₑ ^ p with hψ2
  have hψ1m : Measurable ψ1 :=
    ((hΨ.sub (hG.comp measurable_fst)).enorm).pow_const p
  have hψ2m : Measurable ψ2 := hV.enorm.pow_const p
  -- per-environment Efron–Stein, raised to the power p
  have hper : ∀ y, ∫⁻ v, ψ1 (y, v) ∂π ≤ ENNReal.ofReal Cp ^ p * ∫⁻ v, ψ2 (y, v) ∂π := by
    intro y
    have h := hES (Ψ y) (hmem y).1 (hmem y)
    have h' := ENNReal.rpow_le_rpow h hp'
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp', aux_lem_15_u_eLpNorm_rpow π hp,
      aux_lem_15_u_eLpNorm_rpow π hp] at h'
    exact h'
  have hT0 : Measurable (fun ω : I → X => T (ω k0)) := hT.comp (measurable_pi_apply k0)
  have htr1 := aux_lem_15_u_transfer μs k0 base hbase hinv T hT π hπ ψ1 hψ1m
  have htr2 := aux_lem_15_u_transfer μs k0 base hbase hinv T hT π hπ ψ2 hψ2m
  have hmain : ∫⁻ ω, ψ1 (base ω, T (ω k0)) ∂P ≤
      ENNReal.ofReal Cp ^ p * ∫⁻ ω, ψ2 (base ω, T (ω k0)) ∂P := by
    rw [htr1, htr2, ← lintegral_const_mul']
    · exact lintegral_mono fun ω => hper (base ω)
    · exact ENNReal.rpow_ne_top_of_nonneg hp' ENNReal.ofReal_ne_top
  rw [aux_lem_15_u_eLpNorm_eq_rpow P hp, aux_lem_15_u_eLpNorm_eq_rpow P hp]
  have hp1 : (0 : ℝ) ≤ 1 / p := by positivity
  calc (∫⁻ ω, ‖Ψ (base ω) (T (ω k0)) - ∫ v, Ψ (base ω) v ∂π‖ₑ ^ p ∂P) ^ (1 / p)
      = (∫⁻ ω, ψ1 (base ω, T (ω k0)) ∂P) ^ (1 / p) := rfl
    _ ≤ (ENNReal.ofReal Cp ^ p * ∫⁻ ω, ψ2 (base ω, T (ω k0)) ∂P) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hmain hp1
    _ = ENNReal.ofReal Cp * (∫⁻ ω, ψ2 (base ω, T (ω k0)) ∂P) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp1, ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne',
          ENNReal.rpow_one]
    _ = ENNReal.ofReal Cp *
          (∫⁻ ω, ‖Real.sqrt (∑ i : Fin m, ∫ y : X,
            (Ψ (base ω) (T (ω k0)) - Ψ (base ω) (Function.update (T (ω k0)) i y)) ^ 2 ∂μk i)‖ₑ
              ^ p ∂P) ^ (1 / p) := rfl


variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- Almost-everywhere values of a finite sum in `Lp`. -/
theorem aux_lem_15_u_coeFn_sum {ι : Type*} (s : Finset ι)
    (F : ι → Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d)))) :
    ((∑ i ∈ s, F i : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d)))) :
        SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      filter_upwards [Lp.coeFn_zero ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d)))]
        with x hx
      simpa using hx
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j), ih] with x h1 h2
      rw [h1, Pi.add_apply, h2, Finset.sum_insert hi]

/-! ## The grid potentials -/

section Grid

variable (S : ResponseSpace Q) (dir : Bool) (bd : weakSobolevGraph Q) (L : S.space →L[ℝ] ℝ)
  (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt) (hQQt : (Q : Set (SpatialCoordinates d)) ⊆ Qt)
  (a : SpatialCoordinates d) (ell w : ℝ) {m : ℕ} (idx : Fin m → (Fin d → ℤ))

/-- The response of the exponential of a bounded potential. -/
def aux_lem_15_u_R (h : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d)))) : ℝ :=
  aux_lem_15_u_resp S dir bd L (expPotentialCoefficient h)

/-- `1·f` in `L∞(Q)`. -/
def aux_lem_15_u_embU (f : C(SpatialCoordinates d, ℝ)) :
    Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d))) :=
  aux_lem_15_u_emb Qt hQt hQQt Set.univ MeasurableSet.univ f

/-- `1_{C_k}·f` in `L∞(Q)`. -/
def aux_lem_15_u_embC (k : Fin m) (f : C(SpatialCoordinates d, ℝ)) :
    Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d))) :=
  aux_lem_15_u_emb Qt hQt hQQt (aux_lem_15_u_core a ell w (idx k))
    (aux_lem_15_u_core_isOpen a ell w (idx k)).measurableSet f

/-- `1_{strips}·f` in `L∞(Q)`. -/
def aux_lem_15_u_embS (f : C(SpatialCoordinates d, ℝ)) :
    Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d))) :=
  aux_lem_15_u_emb Qt hQt hQQt (aux_lem_15_u_stripSet a ell w)
    (aux_lem_15_u_stripSet_measurable a ell w) f

/-- The grid potential `1·f + Σ_k 1_{C_k} v_k`. -/
def aux_lem_15_u_pot (f : C(SpatialCoordinates d, ℝ)) (v : Fin m → C(SpatialCoordinates d, ℝ)) :
    Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d))) :=
  aux_lem_15_u_embU Qt hQt hQQt f + ∑ k, aux_lem_15_u_embC Qt hQt hQQt a ell w idx k (v k)

/-- The response of the grid potential (the deleted response `Ŷ` at the pieces). -/
def aux_lem_15_u_Psi (f : C(SpatialCoordinates d, ℝ)) (v : Fin m → C(SpatialCoordinates d, ℝ)) :
    ℝ :=
  aux_lem_15_u_R S dir bd L (aux_lem_15_u_pot Qt hQt hQQt a ell w idx f v)

theorem aux_lem_15_u_pot_continuous :
    Continuous (fun fv : C(SpatialCoordinates d, ℝ) × (Fin m → C(SpatialCoordinates d, ℝ)) =>
      aux_lem_15_u_pot Qt hQt hQQt a ell w idx fv.1 fv.2) := by
  unfold aux_lem_15_u_pot aux_lem_15_u_embU aux_lem_15_u_embC
  refine ((aux_lem_15_u_emb_continuous Qt hQt hQQt _ _).comp continuous_fst).add ?_
  refine continuous_finset_sum _ fun k _ => ?_
  exact (aux_lem_15_u_emb_continuous Qt hQt hQQt _ _).comp
    ((continuous_apply k).comp continuous_snd)

theorem aux_lem_15_u_Psi_continuous :
    Continuous (fun fv : C(SpatialCoordinates d, ℝ) × (Fin m → C(SpatialCoordinates d, ℝ)) =>
      aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx fv.1 fv.2) :=
  (aux_lem_15_u_resp_continuous S dir bd L).comp
    (aux_lem_15_u_pot_continuous Qt hQt hQQt a ell w idx)

/-- Replacing the `k`-th piece changes the grid potential only by `1_{C_k}(y - v_k)`. -/
theorem aux_lem_15_u_pot_update (f : C(SpatialCoordinates d, ℝ))
    (v : Fin m → C(SpatialCoordinates d, ℝ)) (k : Fin m) (y : C(SpatialCoordinates d, ℝ)) :
    aux_lem_15_u_pot Qt hQt hQQt a ell w idx f (Function.update v k y) =
      aux_lem_15_u_pot Qt hQt hQQt a ell w idx f v +
        aux_lem_15_u_embC Qt hQt hQQt a ell w idx k (y - v k) := by
  classical
  unfold aux_lem_15_u_pot
  have hterm : ∀ i : Fin m,
      aux_lem_15_u_embC Qt hQt hQQt a ell w idx i (Function.update v k y i) =
        aux_lem_15_u_embC Qt hQt hQQt a ell w idx i (v i) +
          (if i = k then aux_lem_15_u_embC Qt hQt hQQt a ell w idx k (y - v k) else 0) := by
    intro i
    by_cases hik : i = k
    · subst hik
      simp only [Function.update_self, ↓reduceIte]
      unfold aux_lem_15_u_embC
      rw [aux_lem_15_u_emb_sub]
      abel
    · simp [hik]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]
  abel

theorem aux_lem_15_u_embC_supp (k : Fin m) (g : C(SpatialCoordinates d, ℝ)) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∉ aux_lem_15_u_core a ell w (idx k) →
        (aux_lem_15_u_embC Qt hQt hQQt a ell w idx k g : SpatialCoordinates d → ℝ) x = 0 := by
  filter_upwards [aux_lem_15_u_emb_coeFn Qt hQt hQQt _
    (aux_lem_15_u_core_isOpen a ell w (idx k)).measurableSet g] with x hx hxC
  unfold aux_lem_15_u_embC
  rw [hx, Set.indicator_of_notMem hxC]

theorem aux_lem_15_u_embS_supp (g : C(SpatialCoordinates d, ℝ)) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∉ aux_lem_15_u_stripSet a ell w →
        (aux_lem_15_u_embS Qt hQt hQQt a ell w g : SpatialCoordinates d → ℝ) x = 0 := by
  filter_upwards [aux_lem_15_u_emb_coeFn Qt hQt hQQt _
    (aux_lem_15_u_stripSet_measurable a ell w) g] with x hx hxC
  unfold aux_lem_15_u_embS
  rw [hx, Set.indicator_of_notMem hxC]

/-- The clamped piece of a field has sup over `Qt` at most that of the field. -/
theorem aux_lem_15_u_localize_norm_le (hwl : w ≤ ell) (k : Fin m)
    (hkbox : aux_lem_15_u_kbox a ell w (idx k) ⊆ Qt) (η : C(SpatialCoordinates d, ℝ)) :
    haveI : CompactSpace Qt := isCompact_iff_compactSpace.mp hQt
    ‖(aux_lem_15_u_localize a ell w (idx k) η).restrict Qt‖ ≤ ‖η.restrict Qt‖ := by
  haveI : CompactSpace Qt := isCompact_iff_compactSpace.mp hQt
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
  have hmem : aux_lem_15_u_clamp a ell w (idx k) x ∈ Qt :=
    hkbox (aux_lem_15_u_clamp_mem a hwl (idx k) x)
  exact ContinuousMap.norm_coe_le_norm (η.restrict Qt) ⟨_, hmem⟩

/-- **Deletion identity.**  At the pieces of `η`, the grid potential is the original
potential `1·(f + η)` minus `1_{strips} η`. -/
theorem aux_lem_15_u_pot_pieces
    (hell : 0 < ell) (hw : 0 < w)
    (hinj : Function.Injective idx)
    (hcover : ∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ aux_lem_15_u_stripSet a ell w →
      ∃ k, x ∈ aux_lem_15_u_core a ell w (idx k))
    (f η : C(SpatialCoordinates d, ℝ)) :
    aux_lem_15_u_pot Qt hQt hQQt a ell w idx f
        (fun k => aux_lem_15_u_localize a ell w (idx k) η) =
      aux_lem_15_u_embU Qt hQt hQQt (f + η) - aux_lem_15_u_embS Qt hQt hQQt a ell w η := by
  classical
  apply Lp.ext
  have hC : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), ∀ k : Fin m,
      (aux_lem_15_u_embC Qt hQt hQQt a ell w idx k
        (aux_lem_15_u_localize a ell w (idx k) η) : SpatialCoordinates d → ℝ) x =
        (aux_lem_15_u_core a ell w (idx k)).indicator
          (aux_lem_15_u_localize a ell w (idx k) η) x := by
    rw [ae_all_iff]
    intro k
    exact aux_lem_15_u_emb_coeFn Qt hQt hQQt _ _ _
  filter_upwards [Lp.coeFn_add (aux_lem_15_u_embU Qt hQt hQQt f)
      (∑ k, aux_lem_15_u_embC Qt hQt hQQt a ell w idx k
        (aux_lem_15_u_localize a ell w (idx k) η)),
    aux_lem_15_u_coeFn_sum Finset.univ (fun k => aux_lem_15_u_embC Qt hQt hQQt a ell w idx k
        (aux_lem_15_u_localize a ell w (idx k) η)), hC,
    aux_lem_15_u_emb_coeFn Qt hQt hQQt Set.univ MeasurableSet.univ f,
    aux_lem_15_u_emb_coeFn Qt hQt hQQt Set.univ MeasurableSet.univ (f + η),
    aux_lem_15_u_emb_coeFn Qt hQt hQQt _ (aux_lem_15_u_stripSet_measurable a ell w) η,
    Lp.coeFn_sub (aux_lem_15_u_embU Qt hQt hQQt (f + η)) (aux_lem_15_u_embS Qt hQt hQQt a ell w η),
    ae_restrict_mem Q.isOpen.measurableSet]
    with x hadd hsum hCx hf hfη hS hsub hxQ
  unfold aux_lem_15_u_pot
  rw [hadd, Pi.add_apply, hsum, hsub, Pi.sub_apply]
  unfold aux_lem_15_u_embU aux_lem_15_u_embS
  rw [hf, hfη, hS]
  simp only [Set.indicator_univ, ContinuousMap.add_apply]
  simp only [hCx]
  -- each core term is the plain value of `η`
  have hloc : ∀ k : Fin m, (aux_lem_15_u_core a ell w (idx k)).indicator
      (aux_lem_15_u_localize a ell w (idx k) η) x =
      (aux_lem_15_u_core a ell w (idx k)).indicator η x := by
    intro k
    by_cases hxk : x ∈ aux_lem_15_u_core a ell w (idx k)
    · rw [Set.indicator_of_mem hxk, Set.indicator_of_mem hxk]
      show η (aux_lem_15_u_clamp a ell w (idx k) x) = η x
      rw [aux_lem_15_u_clamp_of_mem a ell w (idx k)
        (aux_lem_15_u_core_subset_kbox a hw.le (idx k) hxk)]
    · rw [Set.indicator_of_notMem hxk, Set.indicator_of_notMem hxk]
  simp only [hloc]
  by_cases hxs : x ∈ aux_lem_15_u_stripSet a ell w
  · have hzero : ∀ k : Fin m, (aux_lem_15_u_core a ell w (idx k)).indicator η x = 0 := by
      intro k
      exact Set.indicator_of_notMem
        (fun hxk => aux_lem_15_u_core_not_strip a hell.le (idx k) hxk hxs) _
    simp only [hzero, Finset.sum_const_zero, Set.indicator_of_mem hxs]
    ring
  · obtain ⟨k0, hk0⟩ := hcover x hxQ hxs
    have hsingle : ∑ k : Fin m, (aux_lem_15_u_core a ell w (idx k)).indicator η x =
        (aux_lem_15_u_core a ell w (idx k0)).indicator η x := by
      apply Finset.sum_eq_single k0
      · intro k _ hk
        refine Set.indicator_of_notMem (fun hxk => ?_) _
        exact Set.disjoint_left.mp
          (aux_lem_15_u_core_disjoint a hell.le hw (hinj.ne hk)) hxk hk0
      · intro h; exact absurd (Finset.mem_univ k0) h
    rw [hsingle, Set.indicator_of_mem hk0, Set.indicator_of_notMem hxs]
    ring

/-- The cores carry at most the response of any coefficient. -/
theorem aux_lem_15_u_sum_cores_le (hell : 0 ≤ ell) (hw : 0 < w)
    (hinj : Function.Injective idx) (c : PositiveCoefficient Q) :
    ∑ k : Fin m, localGradientEnergy c
        (aux_lem_15_u_core_isOpen a ell w (idx k)).measurableSet
        (aux_lem_15_u_grad S dir bd L c) ≤
      aux_lem_15_u_resp S dir bd L c := by
  rw [aux_lem_15_u_resp_eq]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m)))
      (fun k => aux_lem_15_u_core a ell w (idx k)) := by
    intro k _ k' _ hkk'
    exact aux_lem_15_u_core_disjoint a hell hw (hinj.ne hkk')
  exact aux_lem_15_u_sum_local_le Finset.univ (fun k => aux_lem_15_u_core a ell w (idx k))
    (fun k => (aux_lem_15_u_core_isOpen a ell w (idx k)).measurableSet) hdisj c _

end Grid

/-! ## Mass of the perturbed minimizer on a set -/

/-- Paper lines 1453–1460: the perturbed minimizer's mass on any set `C` is controlled
by the original mass on `C` and on the perturbation set `B`. -/
theorem aux_lem_15_u_core_mass (S : ResponseSpace Q) (dir : Bool) (bd : weakSobolevGraph Q)
    (L : S.space →L[ℝ] ℝ)
    (h g : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d))))
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
    (hsupp : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), x ∉ B → g x = 0)
    (C : Set (SpatialCoordinates d)) (hC : MeasurableSet C) :
    localGradientEnergy (expPotentialCoefficient (h + g)) hC
        (aux_lem_15_u_grad S dir bd L (expPotentialCoefficient (h + g))) ≤
      2 * Real.exp ‖g‖ * localGradientEnergy (expPotentialCoefficient h) hC
          (aux_lem_15_u_grad S dir bd L (expPotentialCoefficient h)) +
        2 * (‖g‖ ^ 2 * Real.exp (3 * ‖g‖)) * localGradientEnergy (expPotentialCoefficient h) hB
          (aux_lem_15_u_grad S dir bd L (expPotentialCoefficient h)) := by
  set a := expPotentialCoefficient h
  set b := expPotentialCoefficient (h + g)
  set ga := aux_lem_15_u_grad S dir bd L a
  set gb := aux_lem_15_u_grad S dir bd L b
  have htri := localGradientEnergy_sub_le b hC gb ga
  have hdiff : localGradientEnergy b hC (gb - ga) ≤ weightedGradientForm b.val (gb - ga) (gb - ga) :=
    localGradientEnergy_le b hC _
  have hpert := (aux_lem_15_u_perturb S dir bd L h g B hB hsupp).1
  have hcmp : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      b.val x ≤ Real.exp ‖g‖ * a.val x := by
    have := (expPotentialCoefficient_comparison h (h + g)).2
    filter_upwards [this] with x hx
    have hn : ‖h - (h + g)‖ = ‖g‖ := by rw [sub_add_cancel_left, norm_neg]
    rw [hn] at hx
    exact hx
  have hcmpE := localGradientEnergy_le_mul b a (Real.exp ‖g‖) hcmp hC ga
  have hga : localGradientEnergy b hC ga ≤ Real.exp ‖g‖ * localGradientEnergy a hC ga := hcmpE
  calc localGradientEnergy b hC gb
      ≤ 2 * localGradientEnergy b hC ga + 2 * localGradientEnergy b hC (gb - ga) := htri
    _ ≤ 2 * (Real.exp ‖g‖ * localGradientEnergy a hC ga) +
          2 * (‖g‖ ^ 2 * Real.exp (3 * ‖g‖) * localGradientEnergy a hB ga) := by
        gcongr
        exact hdiff.trans hpert
    _ = _ := by ring


variable {d : ℕ}

/-- The layers other than `-j` in the cutoff potential, minus the normalization. -/
def aux_lem_15_u_base (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N j : ℕ) (lk : ℝ)
    (omega : BilateralField d) : C(SpatialCoordinates d, ℝ) :=
  H omega + (∑ k ∈ (Finset.range (N + 1)).erase j, omega (-(k : ℤ))) -
    ContinuousMap.const _ lk

theorem aux_lem_15_u_base_measurable
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N j : ℕ) (lk : ℝ) :
    Measurable (aux_lem_15_u_base H N j lk) := by
  unfold aux_lem_15_u_base
  refine (hH.add (Finset.measurable_sum _ fun k _ => measurable_pi_apply _)).sub
    measurable_const

theorem aux_lem_15_u_base_update (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N j : ℕ) (lk : ℝ) (omega : BilateralField d) (eta : C(SpatialCoordinates d, ℝ))
    (hH : H (Function.update omega (-(j : ℤ)) eta) = H omega) :
    aux_lem_15_u_base H N j lk (Function.update omega (-(j : ℤ)) eta) =
      aux_lem_15_u_base H N j lk omega := by
  unfold aux_lem_15_u_base
  rw [hH]
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≠ j := Finset.ne_of_mem_erase hk
  have hne : (-(k : ℤ)) ≠ -(j : ℤ) := by
    intro h; apply hkj; exact_mod_cast neg_inj.mp h
  rw [Function.update_of_ne hne]

theorem aux_lem_15_u_cutoff_eq (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N j : ℕ) (hj : j ≤ N) (lk : ℝ) (omega : BilateralField d) (x : SpatialCoordinates d) :
    cutoffPotential H omega N x - lk =
      (aux_lem_15_u_base H N j lk omega + omega (-(j : ℤ))) x := by
  unfold aux_lem_15_u_base cutoffPotential
  have hmem : j ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.sum_apply,
    ContinuousMap.const_apply]
  rw [← Finset.sum_erase_add _ _ hmem]
  simp only [Int.ofNat_eq_natCast]
  ring

/-- The parent's arbitrary positive coefficient is the exponential of the `L∞` class of
`base ω + g_{-j}`. -/
theorem aux_lem_15_u_coeff_eq {Q : Opens (SpatialCoordinates d)}
    (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt)
    (hQQt : (Q : Set (SpatialCoordinates d)) ⊆ Qt)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N j : ℕ) (hj : j ≤ N) (kap : ℝ)
    (omega : BilateralField d) (c : PositiveCoefficient Q)
    (hc : c.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      (fun x => Real.exp (cutoffPotential H omega N x - Real.log kap))) :
    c = expPotentialCoefficient (aux_lem_15_u_embU Qt hQt hQQt
      (aux_lem_15_u_base H N j (Real.log kap) omega + omega (-(j : ℤ)))) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [hc, expPotentialCoefficient_coeFn (aux_lem_15_u_embU Qt hQt hQQt
      (aux_lem_15_u_base H N j (Real.log kap) omega + omega (-(j : ℤ)))),
    aux_lem_15_u_emb_coeFn Qt hQt hQQt Set.univ MeasurableSet.univ
      (aux_lem_15_u_base H N j (Real.log kap) omega + omega (-(j : ℤ)))] with x h1 h2 h3
  rw [h1, h2]
  unfold aux_lem_15_u_embU
  rw [h3, Set.indicator_univ, aux_lem_15_u_cutoff_eq H N j hj]

/-! ## Energy-measure form of the growth bound and of `lem_strips` -/

/-- The strip and core consequences of `lem_strips` for one growth constant. -/
def aux_lem_15_u_StripBound (Q : Opens (SpatialCoordinates d)) (t : ℝ) (a : SpatialCoordinates d)
    (ell w Astrip Acore : ℝ) : Prop :=
  ∀ (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu] (Kv : ℝ), 0 ≤ Kv →
    (∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
      nu (Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d))) ≤ ENNReal.ofReal (Kv * rad ^ t)) →
    nu ((Q : Set (SpatialCoordinates d)) ∩ aux_lem_15_u_stripSet a ell w) ≤
        ENNReal.ofReal (Astrip * Kv) ∧
      ∀ idx : Fin d → ℤ,
        nu ((Q : Set (SpatialCoordinates d)) ∩
          {x | ∀ i : Fin d, a i + (idx i : ℝ) * ell ≤ x i ∧ x i < a i + ((idx i : ℝ) + 1) * ell})
          ≤ ENNReal.ofReal (Acore * Kv)

theorem aux_lem_15_u_growth_masses {Q : Opens (SpatialCoordinates d)} (t : ℝ)
    (a : SpatialCoordinates d) (ell w Astrip Acore : ℝ)
    (hSB : aux_lem_15_u_StripBound Q t a ell w Astrip Acore) (hw : 0 ≤ w)
    (hAs : 0 ≤ Astrip) (hAc : 0 ≤ Acore)
    (c : PositiveCoefficient Q) (gr : HilbertGradient Q) (Kv : ℝ) (hK : 0 ≤ Kv)
    (hgrowth : ∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      localGradientEnergy c (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet gr ≤
        Kv * rho ^ t) :
    localGradientEnergy c (aux_lem_15_u_stripSet_measurable a ell w) gr ≤ Astrip * Kv ∧
      ∀ idx : Fin d → ℤ, localGradientEnergy c
        (aux_lem_15_u_core_isOpen a ell w idx).measurableSet gr ≤ Acore * Kv := by
  have hQm : MeasurableSet (Q : Set (SpatialCoordinates d)) := Q.isOpen.measurableSet
  have hnu := hSB (aux_lem_15_u_energyMeasure c gr) Kv hK (by
    intro x hx rad hrad hrad1
    rw [aux_lem_15_u_energyMeasure_inter,
      aux_lem_15_u_energyMeasure_apply c gr Metric.isOpen_ball.measurableSet]
    exact ENNReal.ofReal_le_ofReal (hgrowth x hx rad hrad hrad1))
  obtain ⟨hstrip, hcore⟩ := hnu
  constructor
  · have h := hstrip
    rw [Set.inter_comm, aux_lem_15_u_energyMeasure_inter,
      aux_lem_15_u_energyMeasure_apply c gr (aux_lem_15_u_stripSet_measurable a ell w)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hAs hK)).1 h
  · intro idx
    have hsub : aux_lem_15_u_core a ell w idx ∩ (Q : Set (SpatialCoordinates d)) ⊆
        (Q : Set (SpatialCoordinates d)) ∩
          {x | ∀ i : Fin d, a i + (idx i : ℝ) * ell ≤ x i ∧
            x i < a i + ((idx i : ℝ) + 1) * ell} := by
      rintro x ⟨hxC, hxQ⟩
      refine ⟨hxQ, fun i => ?_⟩
      obtain ⟨h1, h2⟩ := hxC i
      constructor <;> linarith
    have h := (measure_mono hsub).trans (hcore idx)
    rw [aux_lem_15_u_energyMeasure_inter,
      aux_lem_15_u_energyMeasure_apply c gr (aux_lem_15_u_core_isOpen a ell w idx).measurableSet]
      at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hAc hK)).1 h


variable {d : ℕ}

/-- `sup_{Qt} |f|` for a compact `Qt`. -/
def aux_lem_15_u_supn (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt)
    (f : C(SpatialCoordinates d, ℝ)) : ℝ :=
  haveI : CompactSpace Qt := isCompact_iff_compactSpace.mp hQt
  ‖f.restrict Qt‖

theorem aux_lem_15_u_supn_nonneg (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt)
    (f : C(SpatialCoordinates d, ℝ)) : 0 ≤ aux_lem_15_u_supn Qt hQt f := by
  haveI : CompactSpace Qt := isCompact_iff_compactSpace.mp hQt
  exact norm_nonneg (f.restrict Qt)

theorem aux_lem_15_u_supn_continuous (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt) :
    Continuous (aux_lem_15_u_supn Qt hQt) := by
  haveI : CompactSpace Qt := isCompact_iff_compactSpace.mp hQt
  exact continuous_norm.comp (ContinuousMap.continuous_restrict Qt)

theorem aux_lem_15_u_supn_sub_le (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt)
    (f g : C(SpatialCoordinates d, ℝ)) :
    aux_lem_15_u_supn Qt hQt (f - g) ≤ aux_lem_15_u_supn Qt hQt f + aux_lem_15_u_supn Qt hQt g := by
  haveI : CompactSpace Qt := isCompact_iff_compactSpace.mp hQt
  have hr : (f - g).restrict Qt = f.restrict Qt - g.restrict Qt := ContinuousMap.ext fun _ => rfl
  show ‖(f - g).restrict Qt‖ ≤ ‖f.restrict Qt‖ + ‖g.restrict Qt‖
  rw [hr]
  exact norm_sub_le _ _

theorem aux_lem_15_u_supn_eq_sSup (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt)
    (f : C(SpatialCoordinates d, ℝ)) :
    aux_lem_15_u_supn Qt hQt f = sSup ((fun x : SpatialCoordinates d => ‖f x‖) '' Qt) := by
  haveI : CompactSpace Qt := isCompact_iff_compactSpace.mp hQt
  rw [aux_lem_15_layer_tail_sSup_eq_iSup, aux_lem_15_layer_tail_iSup_eq_norm]
  rfl

theorem aux_lem_15_u_mono_mul_exp {x y c : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hc : 0 ≤ c) :
    x * Real.exp (c * x) ≤ y * Real.exp (c * y) :=
  mul_le_mul hxy (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxy hc)) (Real.exp_pos _).le
    (hx.trans hxy)

theorem aux_lem_15_u_mono_sq_exp {x y c : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hc : 0 ≤ c) :
    x ^ 2 * Real.exp (c * x) ≤ y ^ 2 * Real.exp (c * y) :=
  mul_le_mul (pow_le_pow_left₀ hx hxy 2) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxy hc))
    (Real.exp_pos _).le (by positivity)

/-- **Per-environment diagonal bounds.** -/
theorem aux_lem_15_u_diag {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q) (dir : Bool)
    (bd : weakSobolevGraph Q) (L : S.space →L[ℝ] ℝ)
    (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt)
    (hQQt : (Q : Set (SpatialCoordinates d)) ⊆ Qt)
    (a : SpatialCoordinates d) (ell w : ℝ) (hell : 0 < ell) (hw : 0 < w) (hwl : w ≤ ell)
    {m : ℕ} (idx : Fin m → (Fin d → ℤ)) (hinj : Function.Injective idx)
    (hcover : ∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ aux_lem_15_u_stripSet a ell w →
      ∃ k, x ∈ aux_lem_15_u_core a ell w (idx k))
    (hkbox : ∀ k, aux_lem_15_u_kbox a ell w (idx k) ⊆ Qt)
    (t Astrip Acore : ℝ) (hSB : aux_lem_15_u_StripBound Q t a ell w Astrip Acore)
    (hAs : 0 ≤ Astrip) (hAc : 0 ≤ Acore)
    (f η : C(SpatialCoordinates d, ℝ)) (Kv : ℝ) (hK : 0 ≤ Kv)
    (hgrowth : ∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      localGradientEnergy (expPotentialCoefficient (aux_lem_15_u_embU Qt hQt hQQt (f + η)))
        (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
        (aux_lem_15_u_grad S dir bd L
          (expPotentialCoefficient (aux_lem_15_u_embU Qt hQt hQQt (f + η)))) ≤ Kv * rho ^ t) :
    |aux_lem_15_u_R S dir bd L (aux_lem_15_u_embU Qt hQt hQQt (f + η)) -
        aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx f
          (fun k => aux_lem_15_u_localize a ell w (idx k) η)| ≤
      2 * aux_lem_15_u_supn Qt hQt η * Real.exp (4 * aux_lem_15_u_supn Qt hQt η) *
        (Astrip * Kv) ∧
    aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx f
        (fun k => aux_lem_15_u_localize a ell w (idx k) η) ≤
      Real.exp (aux_lem_15_u_supn Qt hQt η) *
        aux_lem_15_u_R S dir bd L (aux_lem_15_u_embU Qt hQt hQQt (f + η)) ∧
    (∀ k, localGradientEnergy (expPotentialCoefficient (aux_lem_15_u_pot Qt hQt hQQt a ell w idx f
          (fun k => aux_lem_15_u_localize a ell w (idx k) η)))
        (aux_lem_15_u_core_isOpen a ell w (idx k)).measurableSet
        (aux_lem_15_u_grad S dir bd L (expPotentialCoefficient (aux_lem_15_u_pot Qt hQt hQQt
          a ell w idx f (fun k => aux_lem_15_u_localize a ell w (idx k) η)))) ≤
      2 * Real.exp (aux_lem_15_u_supn Qt hQt η) * (Acore * Kv) +
        2 * (aux_lem_15_u_supn Qt hQt η ^ 2 * Real.exp (3 * aux_lem_15_u_supn Qt hQt η)) *
          (Astrip * Kv)) ∧
    (∑ k, localGradientEnergy (expPotentialCoefficient (aux_lem_15_u_pot Qt hQt hQQt a ell w idx f
          (fun k => aux_lem_15_u_localize a ell w (idx k) η)))
        (aux_lem_15_u_core_isOpen a ell w (idx k)).measurableSet
        (aux_lem_15_u_grad S dir bd L (expPotentialCoefficient (aux_lem_15_u_pot Qt hQt hQQt
          a ell w idx f (fun k => aux_lem_15_u_localize a ell w (idx k) η)))) ≤
      aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx f
        (fun k => aux_lem_15_u_localize a ell w (idx k) η)) ∧
    (∀ k (y : C(SpatialCoordinates d, ℝ)),
      |aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx f
          (Function.update (fun k => aux_lem_15_u_localize a ell w (idx k) η) k y) -
        aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx f
          (fun k => aux_lem_15_u_localize a ell w (idx k) η)| ≤
      2 * (aux_lem_15_u_supn Qt hQt y + aux_lem_15_u_supn Qt hQt η) *
        Real.exp (4 * (aux_lem_15_u_supn Qt hQt y + aux_lem_15_u_supn Qt hQt η)) *
        localGradientEnergy (expPotentialCoefficient (aux_lem_15_u_pot Qt hQt hQQt a ell w idx f
          (fun k => aux_lem_15_u_localize a ell w (idx k) η)))
          (aux_lem_15_u_core_isOpen a ell w (idx k)).measurableSet
          (aux_lem_15_u_grad S dir bd L (expPotentialCoefficient (aux_lem_15_u_pot Qt hQt hQQt
            a ell w idx f (fun k => aux_lem_15_u_localize a ell w (idx k) η))))) := by
  set v0 : Fin m → C(SpatialCoordinates d, ℝ) :=
    fun k => aux_lem_15_u_localize a ell w (idx k) η with hv0
  set Sη := aux_lem_15_u_supn Qt hQt η with hSη
  have hSη0 : 0 ≤ Sη := aux_lem_15_u_supn_nonneg Qt hQt η
  set h := aux_lem_15_u_embU Qt hQt hQQt (f + η) with hh
  set g := -(aux_lem_15_u_embS Qt hQt hQQt a ell w η) with hg
  have hpot : aux_lem_15_u_pot Qt hQt hQQt a ell w idx f v0 = h + g := by
    rw [hv0, aux_lem_15_u_pot_pieces Qt hQt hQQt a ell w idx hell hw hinj hcover f η, hh, hg,
      sub_eq_add_neg]
  have hgn : ‖g‖ ≤ Sη := by
    rw [hg, norm_neg]
    exact aux_lem_15_u_emb_norm_le Qt hQt hQQt _ _ η
  have hg0 : 0 ≤ ‖g‖ := norm_nonneg _
  have hgsupp : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∉ aux_lem_15_u_stripSet a ell w → g x = 0 := by
    filter_upwards [aux_lem_15_u_embS_supp Qt hQt hQQt a ell w η,
      Lp.coeFn_neg (aux_lem_15_u_embS Qt hQt hQQt a ell w η)] with x hx hneg hxs
    rw [hg, hneg, Pi.neg_apply, hx hxs, neg_zero]
  have hmass := aux_lem_15_u_growth_masses t a ell w Astrip Acore hSB hw.le hAs hAc
    (expPotentialCoefficient h) (aux_lem_15_u_grad S dir bd L (expPotentialCoefficient h)) Kv hK
    hgrowth
  obtain ⟨hstripm, hcorem⟩ := hmass
  have hmstrip0 : 0 ≤ localGradientEnergy (expPotentialCoefficient h)
      (aux_lem_15_u_stripSet_measurable a ell w)
      (aux_lem_15_u_grad S dir bd L (expPotentialCoefficient h)) :=
    localGradientEnergy_nonneg _ _ _
  have hpert := aux_lem_15_u_perturb S dir bd L h g _ (aux_lem_15_u_stripSet_measurable a ell w)
    hgsupp
  have hPsi : aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx f v0 =
      aux_lem_15_u_resp S dir bd L (expPotentialCoefficient (h + g)) := by
    unfold aux_lem_15_u_Psi aux_lem_15_u_R
    rw [hpot]
  have hR0 : aux_lem_15_u_R S dir bd L h =
      aux_lem_15_u_resp S dir bd L (expPotentialCoefficient h) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- deletion error
    rw [hPsi, hR0, abs_sub_comm]
    refine hpert.2.trans ?_
    have h1 : 2 * ‖g‖ * Real.exp (4 * ‖g‖) ≤ 2 * Sη * Real.exp (4 * Sη) := by
      have := aux_lem_15_u_mono_mul_exp hg0 hgn (by norm_num : (0 : ℝ) ≤ 4)
      nlinarith
    have h2 : 0 ≤ 2 * Sη * Real.exp (4 * Sη) := by positivity
    calc 2 * ‖g‖ * Real.exp (4 * ‖g‖) * localGradientEnergy (expPotentialCoefficient h)
          (aux_lem_15_u_stripSet_measurable a ell w)
          (aux_lem_15_u_grad S dir bd L (expPotentialCoefficient h))
        ≤ 2 * Sη * Real.exp (4 * Sη) * localGradientEnergy (expPotentialCoefficient h)
          (aux_lem_15_u_stripSet_measurable a ell w)
          (aux_lem_15_u_grad S dir bd L (expPotentialCoefficient h)) :=
          mul_le_mul_of_nonneg_right h1 hmstrip0
      _ ≤ 2 * Sη * Real.exp (4 * Sη) * (Astrip * Kv) := mul_le_mul_of_nonneg_left hstripm h2
  · -- multiplicative bound
    rw [hPsi, hR0]
    have hm := (aux_lem_15_u_mult S dir bd L (h + g) h).2
    rw [add_sub_cancel_left] at hm
    refine hm.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hgn)
      (aux_lem_15_u_resp_nonneg _ _ _ _ _))
  · -- deleted masses
    intro k
    rw [hpot]
    have hc := aux_lem_15_u_core_mass S dir bd L h g _ (aux_lem_15_u_stripSet_measurable a ell w)
      hgsupp _ (aux_lem_15_u_core_isOpen a ell w (idx k)).measurableSet
    refine hc.trans ?_
    have hck := hcorem (idx k)
    have hck0 : 0 ≤ localGradientEnergy (expPotentialCoefficient h)
        (aux_lem_15_u_core_isOpen a ell w (idx k)).measurableSet
        (aux_lem_15_u_grad S dir bd L (expPotentialCoefficient h)) :=
      localGradientEnergy_nonneg _ _ _
    have he : Real.exp ‖g‖ ≤ Real.exp Sη := Real.exp_le_exp.mpr hgn
    have hsq : ‖g‖ ^ 2 * Real.exp (3 * ‖g‖) ≤ Sη ^ 2 * Real.exp (3 * Sη) :=
      aux_lem_15_u_mono_sq_exp hg0 hgn (by norm_num)
    gcongr
  · -- cores carry at most the deleted response
    exact aux_lem_15_u_sum_cores_le S dir bd L a ell w idx hell.le hw hinj _
  · -- replacing one piece
    intro k y
    have hup := aux_lem_15_u_pot_update Qt hQt hQQt a ell w idx f v0 k y
    set g' := aux_lem_15_u_embC Qt hQt hQQt a ell w idx k (y - v0 k) with hg'
    have hg'supp : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        x ∉ aux_lem_15_u_core a ell w (idx k) → g' x = 0 :=
      aux_lem_15_u_embC_supp Qt hQt hQQt a ell w idx k (y - v0 k)
    have hpert' := aux_lem_15_u_perturb S dir bd L (aux_lem_15_u_pot Qt hQt hQQt a ell w idx f v0)
      g' _ (aux_lem_15_u_core_isOpen a ell w (idx k)).measurableSet hg'supp
    have hg'n : ‖g'‖ ≤ aux_lem_15_u_supn Qt hQt y + Sη := by
      have h1 : ‖g'‖ ≤ aux_lem_15_u_supn Qt hQt (y - v0 k) :=
        aux_lem_15_u_emb_norm_le Qt hQt hQQt _ _ (y - v0 k)
      have h2 := aux_lem_15_u_supn_sub_le Qt hQt y (v0 k)
      have h3 : aux_lem_15_u_supn Qt hQt (v0 k) ≤ Sη :=
        aux_lem_15_u_localize_norm_le Qt hQt a ell w idx hwl k (hkbox k) η
      linarith
    have hΓ0 : 0 ≤ localGradientEnergy (expPotentialCoefficient
        (aux_lem_15_u_pot Qt hQt hQQt a ell w idx f v0))
        (aux_lem_15_u_core_isOpen a ell w (idx k)).measurableSet
        (aux_lem_15_u_grad S dir bd L (expPotentialCoefficient
          (aux_lem_15_u_pot Qt hQt hQQt a ell w idx f v0))) := localGradientEnergy_nonneg _ _ _
    unfold aux_lem_15_u_Psi aux_lem_15_u_R
    rw [hup]
    refine hpert'.2.trans ?_
    have hsum0 : 0 ≤ aux_lem_15_u_supn Qt hQt y + Sη :=
      add_nonneg (aux_lem_15_u_supn_nonneg Qt hQt y) hSη0
    have h1 : 2 * ‖g'‖ * Real.exp (4 * ‖g'‖) ≤
        2 * (aux_lem_15_u_supn Qt hQt y + Sη) *
          Real.exp (4 * (aux_lem_15_u_supn Qt hQt y + Sη)) := by
      have := aux_lem_15_u_mono_mul_exp (norm_nonneg g') hg'n (by norm_num : (0 : ℝ) ≤ 4)
      nlinarith
    exact mul_le_mul_of_nonneg_right h1 hΓ0


/-- The deletion term in `L^p`. -/
theorem aux_lem_15_u_deletion_Lp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ℝ) (hp : 0 < p)
    (D Sfun K : Ω → ℝ) (hS : AEStronglyMeasurable Sfun P)
    (hK : AEStronglyMeasurable K P) (Astrip : ℝ) (hAs : 0 ≤ Astrip)
    (hpt : ∀ᵐ ω ∂P, |D ω| ≤ 2 * Sfun ω * Real.exp (4 * Sfun ω) * (Astrip * K ω))
    (hK0 : ∀ᵐ ω ∂P, 0 ≤ K ω) (hS0 : ∀ ω, 0 ≤ Sfun ω)
    (Mdel B : ℝ) (hMdel : 0 ≤ Mdel)
    (hmS : eLpNorm (fun ω => Sfun ω * Real.exp (4 * Sfun ω)) (ENNReal.ofReal (2 * p)) P ≤
      ENNReal.ofReal Mdel)
    (hmK : eLpNorm K (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) :
    eLpNorm D (ENNReal.ofReal p) P ≤ ENNReal.ofReal (2 * Astrip * Mdel * B) := by
  have hSe : AEStronglyMeasurable (fun ω => Sfun ω * Real.exp (4 * Sfun ω)) P :=
    hS.mul ((Real.continuous_exp.comp_aestronglyMeasurable (hS.const_mul 4)))
  have hmono : eLpNorm D (ENNReal.ofReal p) P ≤
      eLpNorm (fun ω => (2 * Astrip) * ((Sfun ω * Real.exp (4 * Sfun ω)) * K ω))
        (ENNReal.ofReal p) P := by
    apply eLpNorm_mono_ae
    filter_upwards [hpt, hK0] with ω h1 h2
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine h1.trans (le_of_eq ?_)
    rw [abs_of_nonneg]
    · ring
    · have := hS0 ω
      positivity
  refine hmono.trans ?_
  have hsm : (fun ω => (2 * Astrip) * ((Sfun ω * Real.exp (4 * Sfun ω)) * K ω)) =
      (2 * Astrip) • (fun ω => Sfun ω * Real.exp (4 * Sfun ω) * K ω) := by
    funext ω; simp [smul_eq_mul]
  rw [hsm, eLpNorm_const_smul]
  have hH := aux_lem_15_u_holder hSe hK hp
  have hK2 : eLpNorm K (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal B :=
    (aux_lem_15_u_exponent_mono hK (by linarith)).trans hmK
  calc ‖2 * Astrip‖ₑ * eLpNorm (fun ω => Sfun ω * Real.exp (4 * Sfun ω) * K ω)
        (ENNReal.ofReal p) P
      ≤ ‖2 * Astrip‖ₑ * (ENNReal.ofReal Mdel * ENNReal.ofReal B) := by
        gcongr
        exact hH.trans (mul_le_mul' hmS hK2)
    _ = ENNReal.ofReal (2 * Astrip * Mdel * B) := by
        rw [Real.enorm_eq_ofReal (by positivity), ← ENNReal.ofReal_mul hMdel,
          ← ENNReal.ofReal_mul (by positivity)]
        ring_nf

/-- The pure real inequality behind the three-factor Hölder step. -/
theorem aux_lem_15_u_sqrt_real (c E13 E7 M2 M0 S Kv Y V : ℝ) (hc : 0 ≤ c)
    (hE7 : 0 ≤ E7) (hE : E13 ≤ E7 ^ 2) (hM2 : 0 ≤ M2) (hM0 : 0 ≤ M0) (hS : 0 ≤ S)
    (hK : 0 ≤ Kv) (hY : 0 ≤ Y)
    (hV : V ≤ c * E13 * (M2 + S ^ 2 * M0) * Kv * Y) :
    Real.sqrt V ≤ Real.sqrt c * E7 * (Real.sqrt M2 + S * Real.sqrt M0) * (Kv + Y) := by
  have hs2 : Real.sqrt M2 ^ 2 = M2 := Real.sq_sqrt hM2
  have hs0 : Real.sqrt M0 ^ 2 = M0 := Real.sq_sqrt hM0
  have hsc : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc
  have hA : M2 + S ^ 2 * M0 ≤ (Real.sqrt M2 + S * Real.sqrt M0) ^ 2 := by
    have := mul_nonneg (mul_nonneg hS (Real.sqrt_nonneg M2)) (Real.sqrt_nonneg M0)
    nlinarith
  have hKY : Kv * Y ≤ (Kv + Y) ^ 2 := by nlinarith
  have hrhs : 0 ≤ Real.sqrt c * E7 * (Real.sqrt M2 + S * Real.sqrt M0) * (Kv + Y) := by
    have := Real.sqrt_nonneg c
    have := Real.sqrt_nonneg M2
    have := Real.sqrt_nonneg M0
    positivity
  rw [Real.sqrt_le_left hrhs]
  have hbig : c * E13 * (M2 + S ^ 2 * M0) * Kv * Y ≤
      c * E7 ^ 2 * (Real.sqrt M2 + S * Real.sqrt M0) ^ 2 * (Kv + Y) ^ 2 := by
    have h1 : c * E13 ≤ c * E7 ^ 2 := mul_le_mul_of_nonneg_left hE hc
    have h2 : 0 ≤ M2 + S ^ 2 * M0 := by positivity
    calc c * E13 * (M2 + S ^ 2 * M0) * Kv * Y
        = (c * E13) * (M2 + S ^ 2 * M0) * (Kv * Y) := by ring
      _ ≤ (c * E7 ^ 2) * (Real.sqrt M2 + S * Real.sqrt M0) ^ 2 * (Kv + Y) ^ 2 := by
          gcongr
  calc V ≤ c * E13 * (M2 + S ^ 2 * M0) * Kv * Y := hV
    _ ≤ c * E7 ^ 2 * (Real.sqrt M2 + S * Real.sqrt M0) ^ 2 * (Kv + Y) ^ 2 := hbig
    _ = (Real.sqrt c * E7 * (Real.sqrt M2 + S * Real.sqrt M0) * (Kv + Y)) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, hsc]

/-- The Efron–Stein variance proxy at one environment. -/
theorem aux_lem_15_u_varproxy_le {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {m : ℕ} (Tk : Fin m → Ω → X)
    (hTk : ∀ k, Measurable (Tk k))
    (A : X → ℝ) (hA : Measurable A) (hA0 : ∀ y, 0 ≤ A y)
    (S' : Ω → ℝ) (hAS : ∀ k ω', A (Tk k ω') ≤ S' ω')
    (hI0 : Integrable (fun ω' => Real.exp (8 * S' ω')) P)
    (hI2 : Integrable (fun ω' => S' ω' ^ 2 * Real.exp (8 * S' ω')) P)
    (F : (Fin m → X) → ℝ) (v0 : Fin m → X) (S : ℝ) (hS0 : 0 ≤ S)
    (Γk : Fin m → ℝ)
    (hstep : ∀ k (y : X), |F (Function.update v0 k y) - F v0| ≤
      2 * (A y + S) * Real.exp (4 * (A y + S)) * Γk k) :
    ∑ k : Fin m, ∫ y, (F v0 - F (Function.update v0 k y)) ^ 2 ∂(P.map (Tk k)) ≤
      8 * Real.exp (8 * S) *
        ((∫ ω', S' ω' ^ 2 * Real.exp (8 * S' ω') ∂P) +
          S ^ 2 * ∫ ω', Real.exp (8 * S' ω') ∂P) * ∑ k : Fin m, Γk k ^ 2 := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  -- dominating function on `X`
  set h : X → ℝ := fun y => 8 * Real.exp (8 * S) * Γk k ^ 2 *
    (A y ^ 2 * Real.exp (8 * A y) + S ^ 2 * Real.exp (8 * A y)) with hh
  have hpoint : ∀ y, (F v0 - F (Function.update v0 k y)) ^ 2 ≤ h y := by
    intro y
    have hstp := hstep k y
    have hay := hA0 y
    set s := A y + S with hs
    have hs0 : 0 ≤ s := by positivity
    have habs : |F v0 - F (Function.update v0 k y)| ≤ 2 * s * Real.exp (4 * s) * Γk k := by
      rw [abs_sub_comm]; exact hstp
    have hsq : (F v0 - F (Function.update v0 k y)) ^ 2 ≤
        (2 * s * Real.exp (4 * s) * Γk k) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    refine hsq.trans ?_
    have he : Real.exp (4 * s) ^ 2 = Real.exp (8 * A y) * Real.exp (8 * S) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; rw [hs]; push_cast; ring
    have hs2 : s ^ 2 ≤ 2 * (A y ^ 2 + S ^ 2) := by
      rw [hs]; nlinarith [sq_nonneg (A y - S)]
    have hE : 0 ≤ Real.exp (8 * A y) * Real.exp (8 * S) := by positivity
    have hΓ2 : 0 ≤ Γk k ^ 2 := sq_nonneg _
    calc (2 * s * Real.exp (4 * s) * Γk k) ^ 2
        = 4 * s ^ 2 * (Real.exp (4 * s) ^ 2) * Γk k ^ 2 := by ring
      _ = 4 * s ^ 2 * (Real.exp (8 * A y) * Real.exp (8 * S)) * Γk k ^ 2 := by rw [he]
      _ ≤ 4 * (2 * (A y ^ 2 + S ^ 2)) * (Real.exp (8 * A y) * Real.exp (8 * S)) * Γk k ^ 2 := by
          gcongr
      _ = h y := by rw [hh]; ring
  -- integrability of the dominating function under the image law
  have hAT0 : Integrable (fun ω' => Real.exp (8 * A (Tk k ω'))) P := by
    refine hI0.mono' ((Real.continuous_exp.measurable.comp
      ((hA.comp (hTk k)).const_mul 8)).aestronglyMeasurable) ?_
    filter_upwards with ω'
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith [hAS k ω'])
  have hAT2 : Integrable (fun ω' => A (Tk k ω') ^ 2 * Real.exp (8 * A (Tk k ω'))) P := by
    refine hI2.mono' ((((hA.comp (hTk k)).pow_const 2).mul (Real.continuous_exp.measurable.comp
      ((hA.comp (hTk k)).const_mul 8))).aestronglyMeasurable) ?_
    filter_upwards with ω'
    have h0 := hA0 (Tk k ω')
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact aux_lem_15_u_mono_sq_exp h0 (hAS k ω') (by norm_num)
  have hmapA0 : Integrable (fun y => Real.exp (8 * A y)) (P.map (Tk k)) :=
    (integrable_map_measure ((Real.continuous_exp.measurable.comp
      (hA.const_mul 8)).aestronglyMeasurable) (hTk k).aemeasurable).2 hAT0
  have hmapA2 : Integrable (fun y => A y ^ 2 * Real.exp (8 * A y)) (P.map (Tk k)) :=
    (integrable_map_measure (((hA.pow_const 2).mul (Real.continuous_exp.measurable.comp
      (hA.const_mul 8))).aestronglyMeasurable) (hTk k).aemeasurable).2 hAT2
  have hint_h : Integrable h (P.map (Tk k)) := by
    rw [hh]
    exact (hmapA2.add (hmapA0.const_mul (S ^ 2))).const_mul _
  have hstep1 : ∫ y, (F v0 - F (Function.update v0 k y)) ^ 2 ∂(P.map (Tk k)) ≤
      ∫ y, h y ∂(P.map (Tk k)) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => sq_nonneg _) hint_h
      (Filter.Eventually.of_forall hpoint)
  refine hstep1.trans ?_
  have hm2 : AEStronglyMeasurable (fun y => A y ^ 2 * Real.exp (8 * A y)) (P.map (Tk k)) :=
    ((hA.pow_const 2).mul (Real.continuous_exp.measurable.comp
      (hA.const_mul 8))).aestronglyMeasurable
  have hm0 : AEStronglyMeasurable (fun y => Real.exp (8 * A y)) (P.map (Tk k)) :=
    (Real.continuous_exp.measurable.comp (hA.const_mul 8)).aestronglyMeasurable
  have hcomp : ∫ y, h y ∂(P.map (Tk k)) =
      8 * Real.exp (8 * S) * Γk k ^ 2 *
        ((∫ ω', A (Tk k ω') ^ 2 * Real.exp (8 * A (Tk k ω')) ∂P) +
          S ^ 2 * ∫ ω', Real.exp (8 * A (Tk k ω')) ∂P) := by
    rw [hh, integral_const_mul, integral_add hmapA2 (hmapA0.const_mul _), integral_const_mul,
      integral_map (hTk k).aemeasurable hm2, integral_map (hTk k).aemeasurable hm0]
  rw [hcomp]
  have hle2 : ∫ ω', A (Tk k ω') ^ 2 * Real.exp (8 * A (Tk k ω')) ∂P ≤
      ∫ ω', S' ω' ^ 2 * Real.exp (8 * S' ω') ∂P :=
    integral_mono hAT2 hI2 fun ω' => aux_lem_15_u_mono_sq_exp (hA0 _) (hAS k ω') (by norm_num)
  have hle0 : ∫ ω', Real.exp (8 * A (Tk k ω')) ∂P ≤ ∫ ω', Real.exp (8 * S' ω') ∂P :=
    integral_mono hAT0 hI0 fun ω' => Real.exp_le_exp.mpr (by linarith [hAS k ω'])
  have hc0 : 0 ≤ 8 * Real.exp (8 * S) * Γk k ^ 2 := by positivity
  calc 8 * Real.exp (8 * S) * Γk k ^ 2 *
        ((∫ ω', A (Tk k ω') ^ 2 * Real.exp (8 * A (Tk k ω')) ∂P) +
          S ^ 2 * ∫ ω', Real.exp (8 * A (Tk k ω')) ∂P)
      ≤ 8 * Real.exp (8 * S) * Γk k ^ 2 *
        ((∫ ω', S' ω' ^ 2 * Real.exp (8 * S' ω') ∂P) +
          S ^ 2 * ∫ ω', Real.exp (8 * S' ω') ∂P) := by
        gcongr
    _ = _ := by ring


/-- **Four-term combination.**  The replacement difference is bounded by twice the
deletion error plus twice the centered deleted response. -/
theorem aux_lem_15_u_fourterm {I X Y : Type*} [DecidableEq I] [MeasurableSpace X]
    [MeasurableSpace Y] (μs : I → Measure X) [∀ i, IsProbabilityMeasure (μs i)] (k0 : I)
    (base : (I → X) → Y) (hbase : Measurable base)
    (hinv : ∀ᵐ q ∂((Measure.infinitePi μs).prod (Measure.infinitePi μs)),
      base (Function.update q.1 k0 (q.2 k0)) = base q.1)
    (RN Yh : (I → X) → ℝ) (Gt : Y → ℝ)
    (hRN : AEStronglyMeasurable RN (Measure.infinitePi μs))
    (hYh : AEStronglyMeasurable Yh (Measure.infinitePi μs)) (hGt : Measurable Gt)
    (p : ℝ) (hp : 1 ≤ p) (A1 A2 : ℝ) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (h1 : eLpNorm (fun ω => RN ω - Yh ω) (ENNReal.ofReal p) (Measure.infinitePi μs) ≤
      ENNReal.ofReal A1)
    (h2 : eLpNorm (fun ω => Yh ω - Gt (base ω)) (ENNReal.ofReal p) (Measure.infinitePi μs) ≤
      ENNReal.ofReal A2) :
    eLpNorm (fun q : (I → X) × (I → X) => RN q.1 - RN (Function.update q.1 k0 (q.2 k0)))
        (ENNReal.ofReal p) ((Measure.infinitePi μs).prod (Measure.infinitePi μs)) ≤
      ENNReal.ofReal (2 * A1 + 2 * A2) := by
  set P := Measure.infinitePi μs with hPdef
  set U : (I → X) × (I → X) → (I → X) := fun q => Function.update q.1 k0 (q.2 k0) with hU
  have hUmp : MeasurePreserving U (P.prod P) P := aux_lem_15_u_update_measurePreserving μs k0
  have hfst : MeasurePreserving (Prod.fst : (I → X) × (I → X) → I → X) (P.prod P) P :=
    measurePreserving_fst
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  set F1 : (I → X) → ℝ := fun ω => RN ω - Yh ω with hF1
  set F2 : (I → X) → ℝ := fun ω => Yh ω - Gt (base ω) with hF2
  have hGb : AEStronglyMeasurable (fun ω => Gt (base ω)) P :=
    (hGt.comp hbase).aestronglyMeasurable
  have hF1m : AEStronglyMeasurable F1 P := hRN.sub hYh
  have hF2m : AEStronglyMeasurable F2 P := hYh.sub hGb
  -- the four terms
  have hae : (fun q : (I → X) × (I → X) => RN q.1 - RN (U q)) =ᵐ[P.prod P]
      fun q => ((F1 ∘ Prod.fst) q + (F2 ∘ Prod.fst) q) - ((F2 ∘ U) q + (F1 ∘ U) q) := by
    filter_upwards [hinv] with q hq
    simp only [Function.comp_apply, hF1, hF2, hU]
    rw [hq]
    ring
  rw [eLpNorm_congr_ae hae]
  have hA : AEStronglyMeasurable (fun q => (F1 ∘ Prod.fst) q + (F2 ∘ Prod.fst) q) (P.prod P) :=
    (hF1m.comp_measurePreserving hfst).add (hF2m.comp_measurePreserving hfst)
  have hB' : AEStronglyMeasurable (fun q => (F2 ∘ U) q + (F1 ∘ U) q) (P.prod P) :=
    (hF2m.comp_measurePreserving hUmp).add (hF1m.comp_measurePreserving hUmp)
  have e1 : eLpNorm (F1 ∘ Prod.fst) (ENNReal.ofReal p) (P.prod P) =
      eLpNorm F1 (ENNReal.ofReal p) P := eLpNorm_comp_measurePreserving hF1m hfst
  have e2 : eLpNorm (F2 ∘ Prod.fst) (ENNReal.ofReal p) (P.prod P) =
      eLpNorm F2 (ENNReal.ofReal p) P := eLpNorm_comp_measurePreserving hF2m hfst
  have e3 : eLpNorm (F2 ∘ U) (ENNReal.ofReal p) (P.prod P) =
      eLpNorm F2 (ENNReal.ofReal p) P := eLpNorm_comp_measurePreserving hF2m hUmp
  have e4 : eLpNorm (F1 ∘ U) (ENNReal.ofReal p) (P.prod P) =
      eLpNorm F1 (ENNReal.ofReal p) P := eLpNorm_comp_measurePreserving hF1m hUmp
  calc eLpNorm (fun q => ((F1 ∘ Prod.fst) q + (F2 ∘ Prod.fst) q) - ((F2 ∘ U) q + (F1 ∘ U) q))
        (ENNReal.ofReal p) (P.prod P)
      ≤ eLpNorm (fun q => (F1 ∘ Prod.fst) q + (F2 ∘ Prod.fst) q) (ENNReal.ofReal p) (P.prod P) +
        eLpNorm (fun q => (F2 ∘ U) q + (F1 ∘ U) q) (ENNReal.ofReal p) (P.prod P) :=
        eLpNorm_sub_le hA hB' hp1
    _ ≤ (eLpNorm (F1 ∘ Prod.fst) (ENNReal.ofReal p) (P.prod P) +
          eLpNorm (F2 ∘ Prod.fst) (ENNReal.ofReal p) (P.prod P)) +
        (eLpNorm (F2 ∘ U) (ENNReal.ofReal p) (P.prod P) +
          eLpNorm (F1 ∘ U) (ENNReal.ofReal p) (P.prod P)) := by
        gcongr
        · exact eLpNorm_add_le (hF1m.comp_measurePreserving hfst)
            (hF2m.comp_measurePreserving hfst) hp1
        · exact eLpNorm_add_le (hF2m.comp_measurePreserving hUmp)
            (hF1m.comp_measurePreserving hUmp) hp1
    _ = (eLpNorm F1 (ENNReal.ofReal p) P + eLpNorm F2 (ENNReal.ofReal p) P) +
        (eLpNorm F2 (ENNReal.ofReal p) P + eLpNorm F1 (ENNReal.ofReal p) P) := by
        rw [e1, e2, e3, e4]
    _ ≤ (ENNReal.ofReal A1 + ENNReal.ofReal A2) + (ENNReal.ofReal A2 + ENNReal.ofReal A1) := by
        gcongr
    _ = ENNReal.ofReal (2 * A1 + 2 * A2) := by
        rw [← ENNReal.ofReal_add hA1 hA2, ← ENNReal.ofReal_add hA2 hA1,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- A nonnegative function with bounded `L¹` seminorm has bounded integral. -/
theorem aux_lem_15_u_integral_le_of_eLpNorm_one {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf0 : ∀ x, 0 ≤ f x) (M : ℝ) (hM : 0 ≤ M)
    (hb : eLpNorm f 1 μ ≤ ENNReal.ofReal M) : ∫ x, f x ∂μ ≤ M := by
  by_cases hfi : AEStronglyMeasurable f μ
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfi]
    have h1 : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = eLpNorm f 1 μ := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      apply lintegral_congr
      intro x
      rw [Real.enorm_eq_ofReal (hf0 x)]
    rw [h1]
    calc (eLpNorm f 1 μ).toReal ≤ (ENNReal.ofReal M).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      _ = M := ENNReal.toReal_ofReal hM
  · rw [integral_non_aestronglyMeasurable hfi]; exact hM

theorem aux_lem_15_u_integrable_of_eLpNorm_one {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : AEStronglyMeasurable f μ) (M : ℝ)
    (hb : eLpNorm f 1 μ ≤ ENNReal.ofReal M) : Integrable f μ :=
  memLp_one_iff_integrable.mp ⟨hf, lt_of_le_of_lt hb ENNReal.ofReal_lt_top⟩


theorem aux_lem_15_u_sq_le_two_exp (S : ℝ) (hS : 0 ≤ S) : S ^ 2 ≤ 2 * Real.exp S := by
  have := Real.quadratic_le_exp_of_nonneg hS
  nlinarith

/-- Real bookkeeping: `V ≤ 8e^{8S} M Σ Γ̂_k²`, `Σ Γ̂_k² ≤ max Γ̂ · Ŷ`, `Ŷ ≤ e^S Y`. -/
theorem aux_lem_15_u_Vbound_real (S Kv R Acore Astrip M V X Y' : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ Kv)
    (hR : 0 ≤ R) (hAc : 0 ≤ Acore) (hAs : 0 ≤ Astrip) (hM : 0 ≤ M) (hY'0 : 0 ≤ Y')
    (hX : X ≤ (2 * Real.exp S * (Acore * Kv) +
      2 * (S ^ 2 * Real.exp (3 * S)) * (Astrip * Kv)) * Y')
    (hY' : Y' ≤ Real.exp S * R)
    (hV : V ≤ 8 * Real.exp (8 * S) * M * X) :
    V ≤ 8 * (2 * Acore + 4 * Astrip) * Real.exp (13 * S) * M * Kv * R := by
  set E := Real.exp S with hE
  have hE1 : 1 ≤ E := Real.one_le_exp hS
  have hE0 : 0 ≤ E := by linarith
  have e3 : Real.exp (3 * S) = E ^ 3 := by
    rw [hE, ← Real.exp_nat_mul]; norm_num
  have e8 : Real.exp (8 * S) = E ^ 8 := by
    rw [hE, ← Real.exp_nat_mul]; norm_num
  have e13 : Real.exp (13 * S) = E ^ 13 := by
    rw [hE, ← Real.exp_nat_mul]; norm_num
  rw [e3] at hX
  rw [e8] at hV
  rw [e13]
  have hS2 : S ^ 2 ≤ 2 * E := aux_lem_15_u_sq_le_two_exp S hS
  have hGb0 : 0 ≤ 2 * E * (Acore * Kv) + 2 * (S ^ 2 * E ^ 3) * (Astrip * Kv) := by positivity
  have hGb : 2 * E * (Acore * Kv) + 2 * (S ^ 2 * E ^ 3) * (Astrip * Kv) ≤
      (2 * E * Acore + 4 * E ^ 4 * Astrip) * Kv := by
    have h1 : S ^ 2 * E ^ 3 ≤ 2 * E * E ^ 3 := mul_le_mul_of_nonneg_right hS2 (by positivity)
    have h2 : 2 * (S ^ 2 * E ^ 3) * (Astrip * Kv) ≤ 2 * (2 * E * E ^ 3) * (Astrip * Kv) := by
      gcongr
    nlinarith
  have hX2 : X ≤ (2 * E * Acore + 4 * E ^ 4 * Astrip) * Kv * (E * R) := by
    calc X ≤ (2 * E * (Acore * Kv) + 2 * (S ^ 2 * E ^ 3) * (Astrip * Kv)) * Y' := hX
      _ ≤ (2 * E * Acore + 4 * E ^ 4 * Astrip) * Kv * (E * R) := by
          apply mul_le_mul hGb hY' hY'0
          positivity
  have hE25 : E ^ 2 ≤ E ^ 5 := pow_le_pow_right₀ hE1 (by norm_num)
  have hX3 : X ≤ (2 * Acore + 4 * Astrip) * E ^ 5 * Kv * R := by
    refine hX2.trans ?_
    have : (2 * E * Acore + 4 * E ^ 4 * Astrip) * Kv * (E * R) =
        (2 * E ^ 2 * Acore + 4 * E ^ 5 * Astrip) * (Kv * R) := by ring
    rw [this]
    have h3 : 2 * E ^ 2 * Acore + 4 * E ^ 5 * Astrip ≤ (2 * Acore + 4 * Astrip) * E ^ 5 := by
      nlinarith [mul_le_mul_of_nonneg_left hE25 hAc]
    have hKR : 0 ≤ Kv * R := mul_nonneg hK hR
    nlinarith [mul_le_mul_of_nonneg_right h3 hKR]
  have h8M : 0 ≤ 8 * E ^ 8 * M := by positivity
  calc V ≤ 8 * E ^ 8 * M * X := hV
    _ ≤ 8 * E ^ 8 * M * ((2 * Acore + 4 * Astrip) * E ^ 5 * Kv * R) :=
        mul_le_mul_of_nonneg_left hX3 h8M
    _ = 8 * (2 * Acore + 4 * Astrip) * E ^ 13 * M * Kv * R := by ring


variable {d : ℕ}

/-- The Efron–Stein moment inequality for a finite product law (first conjunct of
`in_efron_stein`). -/
def aux_lem_15_u_ESProp {X : Type*} [MeasurableSpace X] {m : ℕ} (μk : Fin m → Measure X)
    (p Cp : ℝ) : Prop :=
  ∀ F : (Fin m → X) → ℝ, AEStronglyMeasurable F (Measure.pi μk) →
    MemLp F (ENNReal.ofReal p) (Measure.pi μk) →
    eLpNorm (fun x => F x - ∫ y, F y ∂(Measure.pi μk)) (ENNReal.ofReal p) (Measure.pi μk) ≤
      ENNReal.ofReal Cp *
        eLpNorm (fun x => Real.sqrt
          (∑ i : Fin m, ∫ y : X, (F x - F (Function.update x i y)) ^ 2 ∂μk i))
          (ENNReal.ofReal p) (Measure.pi μk)

/-- The growth bound (mfd-4) for the minimizer of `exp h`. -/
def aux_lem_15_u_Growth {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q) (dir : Bool)
    (bd : weakSobolevGraph Q) (L : S.space →L[ℝ] ℝ) (t : ℝ)
    (h : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d)))) (Kv : ℝ) : Prop :=
  ∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
    localGradientEnergy (expPotentialCoefficient h) (s := Metric.ball x rho)
      Metric.isOpen_ball.measurableSet
      (aux_lem_15_u_grad S dir bd L (expPotentialCoefficient h)) ≤ Kv * rho ^ t

/-- The deleted response at the pieces of `η` is at most `e^{2 sup|η|}` times the
response of the other layers. -/
theorem aux_lem_15_u_Psi_pieces_le {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q)
    (dir : Bool) (bd : weakSobolevGraph Q) (L : S.space →L[ℝ] ℝ)
    (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt)
    (hQQt : (Q : Set (SpatialCoordinates d)) ⊆ Qt)
    (a : SpatialCoordinates d) (ell w : ℝ) (hell : 0 < ell) (hw : 0 < w)
    {m : ℕ} (idx : Fin m → (Fin d → ℤ)) (hinj : Function.Injective idx)
    (hcover : ∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ aux_lem_15_u_stripSet a ell w →
      ∃ k, x ∈ aux_lem_15_u_core a ell w (idx k))
    (f η : C(SpatialCoordinates d, ℝ)) :
    0 ≤ aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx f
        (fun k => aux_lem_15_u_localize a ell w (idx k) η) ∧
      aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx f
        (fun k => aux_lem_15_u_localize a ell w (idx k) η) ≤
      Real.exp (2 * aux_lem_15_u_supn Qt hQt η) *
        aux_lem_15_u_R S dir bd L (aux_lem_15_u_embU Qt hQt hQQt f) := by
  constructor
  · exact aux_lem_15_u_resp_nonneg _ _ _ _ _
  · unfold aux_lem_15_u_Psi
    rw [aux_lem_15_u_pot_pieces Qt hQt hQQt a ell w idx hell hw hinj hcover f η]
    have hm := (aux_lem_15_u_mult S dir bd L
      (aux_lem_15_u_embU Qt hQt hQQt (f + η) - aux_lem_15_u_embS Qt hQt hQQt a ell w η)
      (aux_lem_15_u_embU Qt hQt hQQt f)).2
    have hdiff : aux_lem_15_u_embU Qt hQt hQQt (f + η) - aux_lem_15_u_embS Qt hQt hQQt a ell w η -
        aux_lem_15_u_embU Qt hQt hQQt f =
        aux_lem_15_u_embU Qt hQt hQQt η - aux_lem_15_u_embS Qt hQt hQQt a ell w η := by
      unfold aux_lem_15_u_embU
      rw [aux_lem_15_u_emb_add]
      abel
    rw [hdiff] at hm
    have hn : ‖aux_lem_15_u_embU Qt hQt hQQt η - aux_lem_15_u_embS Qt hQt hQQt a ell w η‖ ≤
        2 * aux_lem_15_u_supn Qt hQt η := by
      have h1 : ‖aux_lem_15_u_embU Qt hQt hQQt η‖ ≤ aux_lem_15_u_supn Qt hQt η :=
        aux_lem_15_u_emb_norm_le Qt hQt hQQt _ _ η
      have h2 : ‖aux_lem_15_u_embS Qt hQt hQQt a ell w η‖ ≤ aux_lem_15_u_supn Qt hQt η :=
        aux_lem_15_u_emb_norm_le Qt hQt hQQt _ _ η
      linarith [norm_sub_le (aux_lem_15_u_embU Qt hQt hQQt η)
        (aux_lem_15_u_embS Qt hQt hQQt a ell w η)]
    exact hm.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hn)
      (aux_lem_15_u_resp_nonneg _ _ _ _ _))


variable {d : ℕ}

/-- Real bookkeeping for the variance proxy (sum of squares, deleted response,
three-factor Hölder). -/
theorem aux_lem_15_u_sqrtV_real {m : ℕ} (V Sη Kv R0 Acore Astrip M2 M0 Yh : ℝ)
    (Γ : Fin m → ℝ) (G : ℝ) (hS : 0 ≤ Sη) (hK : 0 ≤ Kv) (hR0 : 0 ≤ R0) (hAc : 0 ≤ Acore)
    (hAs : 0 ≤ Astrip) (hM2 : 0 ≤ M2) (hM0 : 0 ≤ M0) (hYh : 0 ≤ Yh) (hΓ0 : ∀ k, 0 ≤ Γ k)
    (hG : G = 2 * Real.exp Sη * (Acore * Kv) + 2 * (Sη ^ 2 * Real.exp (3 * Sη)) * (Astrip * Kv))
    (hcore : ∀ k, Γ k ≤ G) (hsum : ∑ k, Γ k ≤ Yh) (hmul : Yh ≤ Real.exp Sη * R0)
    (hvp : V ≤ 8 * Real.exp (8 * Sη) * (M2 + Sη ^ 2 * M0) * ∑ k, Γ k ^ 2) :
    Real.sqrt V ≤ Real.sqrt (8 * (2 * Acore + 4 * Astrip)) *
      ((Real.sqrt M2 * Real.exp (7 * Sη) + Real.sqrt M0 * (Sη * Real.exp (7 * Sη))) *
        (Kv + R0)) := by
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have hsq : ∑ k, Γ k ^ 2 ≤ G * Yh := by
    calc ∑ k, Γ k ^ 2 ≤ ∑ k, G * Γ k := by
          apply Finset.sum_le_sum
          intro k _
          rw [sq]
          exact mul_le_mul_of_nonneg_right (hcore k) (hΓ0 k)
      _ = G * ∑ k, Γ k := by rw [Finset.mul_sum]
      _ ≤ G * Yh := mul_le_mul_of_nonneg_left hsum hG0
  rw [hG] at hsq
  have hV := aux_lem_15_u_Vbound_real Sη Kv R0 Acore Astrip (M2 + Sη ^ 2 * M0) V
    (∑ k, Γ k ^ 2) Yh hS hK hR0 hAc hAs (by positivity) hYh hsq hmul hvp
  have hsr := aux_lem_15_u_sqrt_real (8 * (2 * Acore + 4 * Astrip)) (Real.exp (13 * Sη))
    (Real.exp (7 * Sη)) M2 M0 Sη Kv R0 V (by positivity) (Real.exp_pos _).le
    (by
      rw [← Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (by push_cast; nlinarith))
    hM2 hM0 hS hK hR0 hV
  refine hsr.trans (le_of_eq ?_)
  ring

/-- The variance proxy at the diagonal is dominated by an explicit random majorant. -/
theorem aux_lem_15_u_sqrtV_le
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q) (dir : Bool)
    (bd : weakSobolevGraph Q) (L : S.space →L[ℝ] ℝ)
    (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt)
    (hQQt : (Q : Set (SpatialCoordinates d)) ⊆ Qt)
    (P : Measure (BilateralField d)) [IsProbabilityMeasure P] (k0 : ℤ)
    (a : SpatialCoordinates d) (ell w : ℝ) (hell : 0 < ell) (hw : 0 < w) (hwl : w ≤ ell)
    {m : ℕ} (idx : Fin m → (Fin d → ℤ)) (hinj : Function.Injective idx)
    (hcover : ∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ aux_lem_15_u_stripSet a ell w →
      ∃ k, x ∈ aux_lem_15_u_core a ell w (idx k))
    (hkbox : ∀ k, aux_lem_15_u_kbox a ell w (idx k) ⊆ Qt)
    (t Astrip Acore : ℝ) (hSB : aux_lem_15_u_StripBound Q t a ell w Astrip Acore)
    (hAs : 0 ≤ Astrip) (hAc : 0 ≤ Acore)
    (hI0 : Integrable (fun ω' : BilateralField d =>
      Real.exp (8 * aux_lem_15_u_supn Qt hQt (ω' k0))) P)
    (hI2 : Integrable (fun ω' : BilateralField d =>
      aux_lem_15_u_supn Qt hQt (ω' k0) ^ 2 * Real.exp (8 * aux_lem_15_u_supn Qt hQt (ω' k0))) P)
    (f η : C(SpatialCoordinates d, ℝ)) (Kv : ℝ) (hK : 0 ≤ Kv)
    (hg : aux_lem_15_u_Growth S dir bd L t (aux_lem_15_u_embU Qt hQt hQQt (f + η)) Kv) :
    Real.sqrt (∑ i : Fin m, ∫ y, (aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx f
        (fun k => aux_lem_15_u_localize a ell w (idx k) η) -
      aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx f
        (Function.update (fun k => aux_lem_15_u_localize a ell w (idx k) η) i y)) ^ 2
        ∂((P.map (fun ω : BilateralField d => ω k0)).map (aux_lem_15_u_localize a ell w (idx i))))
      ≤ Real.sqrt (8 * (2 * Acore + 4 * Astrip)) *
        ((Real.sqrt (∫ ω', aux_lem_15_u_supn Qt hQt (ω' k0) ^ 2 *
              Real.exp (8 * aux_lem_15_u_supn Qt hQt (ω' k0)) ∂P) *
            Real.exp (7 * aux_lem_15_u_supn Qt hQt η) +
          Real.sqrt (∫ ω', Real.exp (8 * aux_lem_15_u_supn Qt hQt (ω' k0)) ∂P) *
            (aux_lem_15_u_supn Qt hQt η * Real.exp (7 * aux_lem_15_u_supn Qt hQt η))) *
          (Kv + aux_lem_15_u_R S dir bd L (aux_lem_15_u_embU Qt hQt hQQt (f + η)))) := by
  have hdiag := aux_lem_15_u_diag S dir bd L Qt hQt hQQt a ell w hell hw hwl idx hinj hcover
    hkbox t Astrip Acore hSB hAs hAc f η Kv hK hg
  rcases hdiag with ⟨_, hmul, hcore, hsum, hstep⟩
  have hTkm : ∀ k, Measurable (fun ω' : BilateralField d =>
      aux_lem_15_u_localize a ell w (idx k) (ω' k0)) := fun k =>
    (aux_lem_15_u_localize_continuous a ell w (idx k)).measurable.comp (measurable_pi_apply k0)
  have hμ : ∀ k, (P.map (fun ω : BilateralField d => ω k0)).map
      (aux_lem_15_u_localize a ell w (idx k)) =
        P.map (fun ω' : BilateralField d => aux_lem_15_u_localize a ell w (idx k) (ω' k0)) := by
    intro k
    rw [Measure.map_map (aux_lem_15_u_localize_continuous a ell w (idx k)).measurable
      (measurable_pi_apply k0)]
    rfl
  simp only [hμ]
  have hvp := aux_lem_15_u_varproxy_le P
    (fun k ω' => aux_lem_15_u_localize a ell w (idx k) (ω' k0)) hTkm
    (aux_lem_15_u_supn Qt hQt)
    (aux_lem_15_u_supn_continuous Qt hQt).measurable (aux_lem_15_u_supn_nonneg Qt hQt)
    (fun ω' => aux_lem_15_u_supn Qt hQt (ω' k0))
    (fun k ω' => aux_lem_15_u_localize_norm_le Qt hQt a ell w idx hwl k (hkbox k) (ω' k0))
    hI0 hI2 (aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx f)
    (fun k => aux_lem_15_u_localize a ell w (idx k) η) (aux_lem_15_u_supn Qt hQt η)
    (aux_lem_15_u_supn_nonneg Qt hQt η) _ hstep
  refine aux_lem_15_u_sqrtV_real _ _ _ _ _ _ _ _ _ _ _ ?_ hK ?_ hAc hAs ?_ ?_ ?_ ?_ rfl
    hcore hsum hmul hvp
  · exact aux_lem_15_u_supn_nonneg Qt hQt η
  · exact aux_lem_15_u_resp_nonneg _ _ _ _ _
  · exact integral_nonneg fun ω' => by
      have := aux_lem_15_u_supn_nonneg Qt hQt (ω' k0); positivity
  · exact integral_nonneg fun ω' => (Real.exp_pos _).le
  · exact aux_lem_15_u_resp_nonneg _ _ _ _ _
  · exact fun k => localGradientEnergy_nonneg _ _ _


variable {d : ℕ}

/-- `L^p` bound of the random majorant `W = √c e^{7S}(√M₂ + S√M₀)(K + Y)` by Hölder. -/
theorem aux_lem_15_u_W_Lp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ℝ) (hp : 1 ≤ p)
    (S' K R : Ω → ℝ) (hS' : AEStronglyMeasurable S' P) (hK : AEStronglyMeasurable K P)
    (hR : AEStronglyMeasurable R P)
    (c M2 M0 Ma Mb Me Mc B : ℝ) (hMa : 0 ≤ Ma)
    (hMb : 0 ≤ Mb) (hB : 0 ≤ B) (hM2e : M2 ≤ Me) (hM0c : M0 ≤ Mc)
    (hmA : eLpNorm (fun ω => Real.exp (7 * S' ω)) (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal Ma)
    (hmB : eLpNorm (fun ω => S' ω * Real.exp (7 * S' ω)) (ENNReal.ofReal (2 * p)) P ≤
      ENNReal.ofReal Mb)
    (hmK : eLpNorm K (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B)
    (hmR : eLpNorm R (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => Real.sqrt c *
        ((Real.sqrt M2 * Real.exp (7 * S' ω) + Real.sqrt M0 * (S' ω * Real.exp (7 * S' ω))) *
          (K ω + R ω))) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (Real.sqrt c * ((Real.sqrt Me * Ma + Real.sqrt Mc * Mb) * (2 * B))) := by
  have hp0 : 0 < p := by linarith
  have h2p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * p) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hE7 : AEStronglyMeasurable (fun ω => Real.exp (7 * S' ω)) P :=
    Real.continuous_exp.comp_aestronglyMeasurable (hS'.const_mul 7)
  have hSE7 : AEStronglyMeasurable (fun ω => S' ω * Real.exp (7 * S' ω)) P := hS'.mul hE7
  set Xf : Ω → ℝ := fun ω => Real.sqrt M2 * Real.exp (7 * S' ω) +
    Real.sqrt M0 * (S' ω * Real.exp (7 * S' ω)) with hXf
  set Yf : Ω → ℝ := fun ω => K ω + R ω with hYf
  have hXm : AEStronglyMeasurable Xf P := (hE7.const_mul _).add (hSE7.const_mul _)
  have hYm : AEStronglyMeasurable Yf P := hK.add hR
  have hW : (fun ω => Real.sqrt c * (Xf ω * Yf ω)) = (Real.sqrt c) • (fun ω => Xf ω * Yf ω) := by
    funext ω; simp [smul_eq_mul]
  rw [hW, eLpNorm_const_smul]
  have hX : eLpNorm Xf (ENNReal.ofReal (2 * p)) P ≤
      ENNReal.ofReal (Real.sqrt Me * Ma + Real.sqrt Mc * Mb) := by
    have h1 : eLpNorm Xf (ENNReal.ofReal (2 * p)) P ≤
        eLpNorm (fun ω => Real.sqrt M2 * Real.exp (7 * S' ω)) (ENNReal.ofReal (2 * p)) P +
        eLpNorm (fun ω => Real.sqrt M0 * (S' ω * Real.exp (7 * S' ω))) (ENNReal.ofReal (2 * p)) P :=
      eLpNorm_add_le (hE7.const_mul _) (hSE7.const_mul _) h2p
    have e1 : (fun ω => Real.sqrt M2 * Real.exp (7 * S' ω)) =
        (Real.sqrt M2) • (fun ω => Real.exp (7 * S' ω)) := by funext ω; simp [smul_eq_mul]
    have e2 : (fun ω => Real.sqrt M0 * (S' ω * Real.exp (7 * S' ω))) =
        (Real.sqrt M0) • (fun ω => S' ω * Real.exp (7 * S' ω)) := by funext ω; simp [smul_eq_mul]
    rw [e1, e2, eLpNorm_const_smul, eLpNorm_const_smul] at h1
    refine h1.trans ?_
    rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _), Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]
    have hs2 : Real.sqrt M2 ≤ Real.sqrt Me := Real.sqrt_le_sqrt hM2e
    have hs0 : Real.sqrt M0 ≤ Real.sqrt Mc := Real.sqrt_le_sqrt hM0c
    calc ENNReal.ofReal (Real.sqrt M2) *
          eLpNorm (fun ω => Real.exp (7 * S' ω)) (ENNReal.ofReal (2 * p)) P +
        ENNReal.ofReal (Real.sqrt M0) *
          eLpNorm (fun ω => S' ω * Real.exp (7 * S' ω)) (ENNReal.ofReal (2 * p)) P
        ≤ ENNReal.ofReal (Real.sqrt Me) * ENNReal.ofReal Ma +
          ENNReal.ofReal (Real.sqrt Mc) * ENNReal.ofReal Mb := by
          gcongr
      _ = ENNReal.ofReal (Real.sqrt Me * Ma + Real.sqrt Mc * Mb) := by
          rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hY : eLpNorm Yf (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal (2 * B) := by
    have h1 : eLpNorm Yf (ENNReal.ofReal (2 * p)) P ≤
        eLpNorm K (ENNReal.ofReal (2 * p)) P + eLpNorm R (ENNReal.ofReal (2 * p)) P :=
      eLpNorm_add_le hK hR h2p
    have hK2 := (aux_lem_15_u_exponent_mono hK (show 2 * p ≤ 3 * p by linarith)).trans hmK
    have hR2 := (aux_lem_15_u_exponent_mono hR (show 2 * p ≤ 3 * p by linarith)).trans hmR
    refine h1.trans ((add_le_add hK2 hR2).trans_eq ?_)
    rw [← ENNReal.ofReal_add hB hB]; congr 1; ring
  have hH := aux_lem_15_u_holder hXm hYm hp0
  calc ‖Real.sqrt c‖ₑ * eLpNorm (fun ω => Xf ω * Yf ω) (ENNReal.ofReal p) P
      ≤ ‖Real.sqrt c‖ₑ * (ENNReal.ofReal (Real.sqrt Me * Ma + Real.sqrt Mc * Mb) *
          ENNReal.ofReal (2 * B)) := by
        gcongr
        exact hH.trans (mul_le_mul' hX hY)
    _ = ENNReal.ofReal (Real.sqrt c * ((Real.sqrt Me * Ma + Real.sqrt Mc * Mb) * (2 * B))) := by
        rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]


variable {d : ℕ}

/-- The laws of the clamped pieces of coordinate `k0`. -/
def aux_lem_15_u_muk [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (μs : ℤ → Measure C(SpatialCoordinates d, ℝ)) (k0 : ℤ) (a : SpatialCoordinates d)
    (ell w : ℝ) {m : ℕ} (idx : Fin m → (Fin d → ℤ)) (k : Fin m) :
    Measure C(SpatialCoordinates d, ℝ) :=
  ((Measure.infinitePi μs).map (fun ω : BilateralField d => ω k0)).map
    (aux_lem_15_u_localize a ell w (idx k))

theorem aux_lem_15_u_Psi_continuous_right {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (dir : Bool) (bd : weakSobolevGraph Q) (L : S.space →L[ℝ] ℝ)
    (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt)
    (hQQt : (Q : Set (SpatialCoordinates d)) ⊆ Qt)
    (a : SpatialCoordinates d) (ell w : ℝ) {m : ℕ} (idx : Fin m → (Fin d → ℤ))
    (f : C(SpatialCoordinates d, ℝ)) :
    Continuous (aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx f) := by
  have hu : Continuous (Function.uncurry (aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx)) :=
    aux_lem_15_u_Psi_continuous S dir bd L Qt hQt hQQt a ell w idx
  exact hu.uncurry_left f

theorem aux_lem_15_u_Psi_memLp
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q) (dir : Bool)
    (bd : weakSobolevGraph Q) (L : S.space →L[ℝ] ℝ)
    (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt)
    (hQQt : (Q : Set (SpatialCoordinates d)) ⊆ Qt)
    (μs : ℤ → Measure C(SpatialCoordinates d, ℝ)) [∀ i, IsProbabilityMeasure (μs i)] (k0 : ℤ)
    (a : SpatialCoordinates d) (ell w : ℝ) (hell : 0 < ell) (hw : 0 < w)
    {m : ℕ} (idx : Fin m → (Fin d → ℤ)) (hinj : Function.Injective idx)
    (hcover : ∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ aux_lem_15_u_stripSet a ell w →
      ∃ k, x ∈ aux_lem_15_u_core a ell w (idx k))
    (hπ : (Measure.infinitePi μs).map (fun ω : BilateralField d => fun k : Fin m =>
        aux_lem_15_u_localize a ell w (idx k) (ω k0)) =
      Measure.pi (aux_lem_15_u_muk μs k0 a ell w idx))
    (p Mexp : ℝ)
    (hMexp : eLpNorm (fun ω : BilateralField d =>
        Real.exp (2 * aux_lem_15_u_supn Qt hQt (ω k0))) (ENNReal.ofReal p)
      (Measure.infinitePi μs) ≤ ENNReal.ofReal Mexp)
    (f : C(SpatialCoordinates d, ℝ)) :
    MemLp (aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx f)
      (ENNReal.ofReal p) (Measure.pi (aux_lem_15_u_muk μs k0 a ell w idx)) := by
  have hTm : Measurable (fun ω : BilateralField d => fun k : Fin m =>
      aux_lem_15_u_localize a ell w (idx k) (ω k0)) :=
    measurable_pi_lambda _ fun k =>
      (aux_lem_15_u_localize_continuous a ell w (idx k)).measurable.comp (measurable_pi_apply k0)
  have hSm : Measurable (fun ω : BilateralField d => aux_lem_15_u_supn Qt hQt (ω k0)) :=
    (aux_lem_15_u_supn_continuous Qt hQt).measurable.comp (measurable_pi_apply k0)
  have hexp2 : MemLp (fun ω : BilateralField d => Real.exp (2 * aux_lem_15_u_supn Qt hQt (ω k0)))
      (ENNReal.ofReal p) (Measure.infinitePi μs) :=
    ⟨(Real.continuous_exp.measurable.comp (hSm.const_mul 2)).aestronglyMeasurable,
      lt_of_le_of_lt hMexp ENNReal.ofReal_lt_top⟩
  have hΨf := aux_lem_15_u_Psi_continuous_right S dir bd L Qt hQt hQQt a ell w idx f
  rw [← hπ, memLp_map_measure_iff hΨf.measurable.aestronglyMeasurable hTm.aemeasurable]
  refine MemLp.of_le (hexp2.const_mul (aux_lem_15_u_R S dir bd L
    (aux_lem_15_u_embU Qt hQt hQQt f))) (hΨf.measurable.comp hTm).aestronglyMeasurable ?_
  filter_upwards with ω
  have hb := aux_lem_15_u_Psi_pieces_le S dir bd L Qt hQt hQQt a ell w hell hw idx hinj hcover
    f (ω k0)
  have hR0 : 0 ≤ aux_lem_15_u_R S dir bd L (aux_lem_15_u_embU Qt hQt hQQt f) :=
    aux_lem_15_u_resp_nonneg _ _ _ _ _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Function.comp_apply, abs_of_nonneg hb.1,
    abs_of_nonneg (mul_nonneg hR0 (Real.exp_pos _).le)]
  refine hb.2.trans (le_of_eq ?_)
  ring

theorem aux_lem_15_u_es_term
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q) (dir : Bool)
    (bd : weakSobolevGraph Q) (L : S.space →L[ℝ] ℝ)
    (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt)
    (hQQt : (Q : Set (SpatialCoordinates d)) ⊆ Qt)
    (μs : ℤ → Measure C(SpatialCoordinates d, ℝ)) [∀ i, IsProbabilityMeasure (μs i)] (k0 : ℤ)
    (base : BilateralField d → C(SpatialCoordinates d, ℝ)) (hbase : Measurable base)
    (hinv : ∀ᵐ q ∂((Measure.infinitePi μs).prod (Measure.infinitePi μs)),
      base (Function.update q.1 k0 (q.2 k0)) = base q.1)
    (K : BilateralField d → ℝ) (hKm : AEStronglyMeasurable K (Measure.infinitePi μs)) (t : ℝ)
    (hgrowth : ∀ᵐ ω ∂(Measure.infinitePi μs), 0 ≤ K ω ∧
      aux_lem_15_u_Growth S dir bd L t (aux_lem_15_u_embU Qt hQt hQQt (base ω + ω k0)) (K ω))
    (p B : ℝ) (hp : 1 ≤ p) (hB : 0 ≤ B)
    (hmK : eLpNorm K (ENNReal.ofReal (3 * p)) (Measure.infinitePi μs) ≤ ENNReal.ofReal B)
    (hmR : eLpNorm (fun ω : BilateralField d =>
        aux_lem_15_u_R S dir bd L (aux_lem_15_u_embU Qt hQt hQQt (base ω + ω k0)))
      (ENNReal.ofReal (3 * p)) (Measure.infinitePi μs) ≤ ENNReal.ofReal B)
    (a : SpatialCoordinates d) (ell w : ℝ) (hell : 0 < ell) (hw : 0 < w) (hwl : w ≤ ell)
    {m : ℕ} (idx : Fin m → (Fin d → ℤ)) (hinj : Function.Injective idx)
    (hcover : ∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ aux_lem_15_u_stripSet a ell w →
      ∃ k, x ∈ aux_lem_15_u_core a ell w (idx k))
    (hkbox : ∀ k, aux_lem_15_u_kbox a ell w (idx k) ⊆ Qt)
    (Astrip Acore : ℝ) (hSB : aux_lem_15_u_StripBound Q t a ell w Astrip Acore)
    (hAs : 0 ≤ Astrip) (hAc : 0 ≤ Acore)
    (hπ : (Measure.infinitePi μs).map (fun ω : BilateralField d => fun k : Fin m =>
        aux_lem_15_u_localize a ell w (idx k) (ω k0)) =
      Measure.pi (aux_lem_15_u_muk μs k0 a ell w idx))
    (Cp : ℝ) (hCp : 0 ≤ Cp) (hES : aux_lem_15_u_ESProp (aux_lem_15_u_muk μs k0 a ell w idx) p Cp)
    (Mexp Ma Mb Mc Me : ℝ) (hMa0 : 0 ≤ Ma) (hMb0 : 0 ≤ Mb) (hMc0 : 0 ≤ Mc) (hMe0 : 0 ≤ Me)
    (hMexp : eLpNorm (fun ω : BilateralField d =>
        Real.exp (2 * aux_lem_15_u_supn Qt hQt (ω k0))) (ENNReal.ofReal p)
      (Measure.infinitePi μs) ≤ ENNReal.ofReal Mexp)
    (hMa : eLpNorm (fun ω : BilateralField d =>
        Real.exp (7 * aux_lem_15_u_supn Qt hQt (ω k0))) (ENNReal.ofReal (2 * p))
      (Measure.infinitePi μs) ≤ ENNReal.ofReal Ma)
    (hMb : eLpNorm (fun ω : BilateralField d => aux_lem_15_u_supn Qt hQt (ω k0) *
        Real.exp (7 * aux_lem_15_u_supn Qt hQt (ω k0))) (ENNReal.ofReal (2 * p))
      (Measure.infinitePi μs) ≤ ENNReal.ofReal Mb)
    (hMc : eLpNorm (fun ω : BilateralField d =>
        Real.exp (8 * aux_lem_15_u_supn Qt hQt (ω k0))) 1 (Measure.infinitePi μs) ≤
      ENNReal.ofReal Mc)
    (hMe : eLpNorm (fun ω : BilateralField d => aux_lem_15_u_supn Qt hQt (ω k0) ^ 2 *
        Real.exp (8 * aux_lem_15_u_supn Qt hQt (ω k0))) 1 (Measure.infinitePi μs) ≤
      ENNReal.ofReal Me) :
    eLpNorm (fun ω : BilateralField d =>
        aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx (base ω)
          (fun k => aux_lem_15_u_localize a ell w (idx k) (ω k0)) -
        ∫ v, aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx (base ω) v
          ∂(Measure.pi (aux_lem_15_u_muk μs k0 a ell w idx)))
      (ENNReal.ofReal p) (Measure.infinitePi μs) ≤
    ENNReal.ofReal (Cp * (Real.sqrt (8 * (2 * Acore + 4 * Astrip)) *
      ((Real.sqrt Me * Ma + Real.sqrt Mc * Mb) * (2 * B)))) := by
  haveI : IsProbabilityMeasure ((Measure.infinitePi μs).map (fun ω : BilateralField d => ω k0)) :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply k0).aemeasurable
  haveI : ∀ k, IsProbabilityMeasure (aux_lem_15_u_muk μs k0 a ell w idx k) := fun k => by
    unfold aux_lem_15_u_muk
    exact Measure.isProbabilityMeasure_map
      (aux_lem_15_u_localize_continuous a ell w (idx k)).measurable.aemeasurable
  have hp0 : 0 < p := by linarith
  have hTm : Measurable (fun η : C(SpatialCoordinates d, ℝ) => fun k : Fin m =>
      aux_lem_15_u_localize a ell w (idx k) η) :=
    measurable_pi_lambda _ fun k => (aux_lem_15_u_localize_continuous a ell w (idx k)).measurable
  have hΨm : Measurable (Function.uncurry
      (aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx)) :=
    (aux_lem_15_u_Psi_continuous S dir bd L Qt hQt hQQt a ell w idx).measurable
  have hSm : Measurable (fun ω : BilateralField d => aux_lem_15_u_supn Qt hQt (ω k0)) :=
    (aux_lem_15_u_supn_continuous Qt hQt).measurable.comp (measurable_pi_apply k0)
  have hmem := aux_lem_15_u_Psi_memLp S dir bd L Qt hQt hQQt μs k0 a ell w hell hw idx hinj
    hcover hπ p Mexp hMexp
  have hESd := aux_lem_15_u_es_diag μs k0 base hbase hinv (aux_lem_15_u_muk μs k0 a ell w idx)
    (fun η k => aux_lem_15_u_localize a ell w (idx k) η) hTm hπ
    (aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx) hΨm p Cp hp0 hES hmem
  refine hESd.trans ?_
  -- the variance proxy is dominated by the random majorant `W`
  have hI0 : Integrable (fun ω' : BilateralField d =>
      Real.exp (8 * aux_lem_15_u_supn Qt hQt (ω' k0))) (Measure.infinitePi μs) :=
    aux_lem_15_u_integrable_of_eLpNorm_one (Measure.infinitePi μs) _
      (Real.continuous_exp.measurable.comp (hSm.const_mul 8)).aestronglyMeasurable Mc hMc
  have hI2 : Integrable (fun ω' : BilateralField d => aux_lem_15_u_supn Qt hQt (ω' k0) ^ 2 *
      Real.exp (8 * aux_lem_15_u_supn Qt hQt (ω' k0))) (Measure.infinitePi μs) :=
    aux_lem_15_u_integrable_of_eLpNorm_one (Measure.infinitePi μs) _
      ((hSm.pow_const 2).mul (Real.continuous_exp.measurable.comp
        (hSm.const_mul 8))).aestronglyMeasurable Me hMe
  have hM2e : (∫ ω', aux_lem_15_u_supn Qt hQt (ω' k0) ^ 2 * Real.exp (8 * aux_lem_15_u_supn Qt hQt (ω' k0)) ∂(Measure.infinitePi μs)) ≤ Me := aux_lem_15_u_integral_le_of_eLpNorm_one (Measure.infinitePi μs) _
    (fun ω' => by have := aux_lem_15_u_supn_nonneg Qt hQt (ω' k0); positivity) Me hMe0 hMe
  have hM0c : (∫ ω', Real.exp (8 * aux_lem_15_u_supn Qt hQt (ω' k0)) ∂(Measure.infinitePi μs)) ≤ Mc := aux_lem_15_u_integral_le_of_eLpNorm_one (Measure.infinitePi μs) _
    (fun ω' => (Real.exp_pos _).le) Mc hMc0 hMc
  have hRm : Measurable (fun ω : BilateralField d =>
      aux_lem_15_u_R S dir bd L (aux_lem_15_u_embU Qt hQt hQQt (base ω + ω k0))) :=
    ((aux_lem_15_u_resp_continuous S dir bd L).comp
      (aux_lem_15_u_emb_continuous Qt hQt hQQt Set.univ MeasurableSet.univ)).measurable.comp
      (hbase.add (measurable_pi_apply k0))
  have hdom : ∀ᵐ ω ∂(Measure.infinitePi μs),
      ‖Real.sqrt (∑ i : Fin m, ∫ y : C(SpatialCoordinates d, ℝ),
        (aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx (base ω) (fun k => aux_lem_15_u_localize a ell w (idx k) (ω k0)) -
          aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx (base ω)
            (Function.update (fun k => aux_lem_15_u_localize a ell w (idx k) (ω k0)) i y)) ^ 2 ∂(aux_lem_15_u_muk μs k0 a ell w idx i))‖ ≤
      ‖Real.sqrt (8 * (2 * Acore + 4 * Astrip)) *
        ((Real.sqrt (∫ ω', aux_lem_15_u_supn Qt hQt (ω' k0) ^ 2 * Real.exp (8 * aux_lem_15_u_supn Qt hQt (ω' k0)) ∂(Measure.infinitePi μs)) * Real.exp (7 * aux_lem_15_u_supn Qt hQt (ω k0)) +
          Real.sqrt (∫ ω', Real.exp (8 * aux_lem_15_u_supn Qt hQt (ω' k0)) ∂(Measure.infinitePi μs)) * (aux_lem_15_u_supn Qt hQt (ω k0) *
            Real.exp (7 * aux_lem_15_u_supn Qt hQt (ω k0)))) *
          (K ω + aux_lem_15_u_R S dir bd L (aux_lem_15_u_embU Qt hQt hQQt (base ω + ω k0))))‖ := by
    filter_upwards [hgrowth] with ω hω
    obtain ⟨hK0, hg⟩ := hω
    have h := aux_lem_15_u_sqrtV_le S dir bd L Qt hQt hQQt (Measure.infinitePi μs) k0 a ell w hell hw hwl idx hinj
      hcover hkbox t Astrip Acore hSB hAs hAc hI0 hI2 (base ω) (ω k0) (K ω) hK0 hg
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact h.trans (le_abs_self _)
  have hW := aux_lem_15_u_W_Lp (Measure.infinitePi μs) p hp (fun ω => aux_lem_15_u_supn Qt hQt (ω k0)) K
    (fun ω => aux_lem_15_u_R S dir bd L (aux_lem_15_u_embU Qt hQt hQQt (base ω + ω k0)))
    hSm.aestronglyMeasurable hKm hRm.aestronglyMeasurable (8 * (2 * Acore + 4 * Astrip))
    _ _ Ma Mb Me Mc B hMa0 hMb0 hB hM2e hM0c hMa hMb hmK hmR
  calc ENNReal.ofReal Cp * eLpNorm (fun ω => Real.sqrt (∑ i : Fin m,
        ∫ y : C(SpatialCoordinates d, ℝ),
        (aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx (base ω) (fun k => aux_lem_15_u_localize a ell w (idx k) (ω k0)) -
          aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx (base ω)
            (Function.update (fun k => aux_lem_15_u_localize a ell w (idx k) (ω k0)) i y)) ^ 2 ∂(aux_lem_15_u_muk μs k0 a ell w idx i)))
        (ENNReal.ofReal p) (Measure.infinitePi μs)
      ≤ ENNReal.ofReal Cp * ENNReal.ofReal (Real.sqrt (8 * (2 * Acore + 4 * Astrip)) *
          ((Real.sqrt Me * Ma + Real.sqrt Mc * Mb) * (2 * B))) := by
        gcongr
        exact (eLpNorm_mono_ae hdom).trans hW
    _ = ENNReal.ofReal (Cp * (Real.sqrt (8 * (2 * Acore + 4 * Astrip)) *
          ((Real.sqrt Me * Ma + Real.sqrt Mc * Mb) * (2 * B)))) := by
        rw [← ENNReal.ofReal_mul hCp]


variable {d : ℕ}

/-- Measurability of `ω ↦ F (g ω) (h ω)` from joint measurability of `F` (stated for a
variable `F` so that no definition is unfolded during unification). -/
theorem aux_lem_15_u_measurable_uncurry_comp {Ω Y Z : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Y] [MeasurableSpace Z] (F : Y → Z → ℝ) (hF : Measurable (Function.uncurry F))
    (g : Ω → Y) (h : Ω → Z) (hg : Measurable g) (hh : Measurable h) :
    Measurable (fun ω => F (g ω) (h ω)) :=
  hF.comp (hg.prodMk hh)

theorem aux_lem_15_u_masking
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q) (dir : Bool)
    (bd : weakSobolevGraph Q) (L : S.space →L[ℝ] ℝ)
    (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt)
    (hQQt : (Q : Set (SpatialCoordinates d)) ⊆ Qt)
    (μs : ℤ → Measure C(SpatialCoordinates d, ℝ)) [∀ i, IsProbabilityMeasure (μs i)] (k0 : ℤ)
    (base : BilateralField d → C(SpatialCoordinates d, ℝ)) (hbase : Measurable base)
    (hinv : ∀ᵐ q ∂((Measure.infinitePi μs).prod (Measure.infinitePi μs)),
      base (Function.update q.1 k0 (q.2 k0)) = base q.1)
    (RN K : BilateralField d → ℝ)
    (hRN : ∀ ω, RN ω = aux_lem_15_u_R S dir bd L (aux_lem_15_u_embU Qt hQt hQQt (base ω + ω k0)))
    (hKm : AEStronglyMeasurable K (Measure.infinitePi μs)) (t : ℝ)
    (hgrowth : ∀ᵐ ω ∂(Measure.infinitePi μs), 0 ≤ K ω ∧
      aux_lem_15_u_Growth S dir bd L t (aux_lem_15_u_embU Qt hQt hQQt (base ω + ω k0)) (K ω))
    (p B : ℝ) (hp : 1 ≤ p) (hB : 0 ≤ B)
    (hmK : eLpNorm K (ENNReal.ofReal (3 * p)) (Measure.infinitePi μs) ≤ ENNReal.ofReal B)
    (hmR : eLpNorm RN (ENNReal.ofReal (3 * p)) (Measure.infinitePi μs) ≤ ENNReal.ofReal B)
    (a : SpatialCoordinates d) (ell w : ℝ) (hell : 0 < ell) (hw : 0 < w) (hwl : w ≤ ell)
    {m : ℕ} (idx : Fin m → (Fin d → ℤ)) (hinj : Function.Injective idx)
    (hcover : ∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ aux_lem_15_u_stripSet a ell w →
      ∃ k, x ∈ aux_lem_15_u_core a ell w (idx k))
    (hkbox : ∀ k, aux_lem_15_u_kbox a ell w (idx k) ⊆ Qt)
    (Astrip Acore : ℝ) (hSB : aux_lem_15_u_StripBound Q t a ell w Astrip Acore)
    (hAs : 0 ≤ Astrip) (hAc : 0 ≤ Acore)
    (hπ : (Measure.infinitePi μs).map (fun ω : BilateralField d => fun k : Fin m =>
        aux_lem_15_u_localize a ell w (idx k) (ω k0)) =
      Measure.pi (aux_lem_15_u_muk μs k0 a ell w idx))
    (Cp : ℝ) (hCp : 0 ≤ Cp) (hES : aux_lem_15_u_ESProp (aux_lem_15_u_muk μs k0 a ell w idx) p Cp)
    (Mexp Mdel Ma Mb Mc Me : ℝ) (hMdel0 : 0 ≤ Mdel) (hMa0 : 0 ≤ Ma) (hMb0 : 0 ≤ Mb)
    (hMc0 : 0 ≤ Mc) (hMe0 : 0 ≤ Me)
    (hMexp : eLpNorm (fun ω : BilateralField d =>
        Real.exp (2 * aux_lem_15_u_supn Qt hQt (ω k0))) (ENNReal.ofReal p)
      (Measure.infinitePi μs) ≤ ENNReal.ofReal Mexp)
    (hMdel : eLpNorm (fun ω : BilateralField d => aux_lem_15_u_supn Qt hQt (ω k0) *
        Real.exp (4 * aux_lem_15_u_supn Qt hQt (ω k0))) (ENNReal.ofReal (2 * p))
      (Measure.infinitePi μs) ≤ ENNReal.ofReal Mdel)
    (hMa : eLpNorm (fun ω : BilateralField d =>
        Real.exp (7 * aux_lem_15_u_supn Qt hQt (ω k0))) (ENNReal.ofReal (2 * p))
      (Measure.infinitePi μs) ≤ ENNReal.ofReal Ma)
    (hMb : eLpNorm (fun ω : BilateralField d => aux_lem_15_u_supn Qt hQt (ω k0) *
        Real.exp (7 * aux_lem_15_u_supn Qt hQt (ω k0))) (ENNReal.ofReal (2 * p))
      (Measure.infinitePi μs) ≤ ENNReal.ofReal Mb)
    (hMc : eLpNorm (fun ω : BilateralField d =>
        Real.exp (8 * aux_lem_15_u_supn Qt hQt (ω k0))) 1 (Measure.infinitePi μs) ≤
      ENNReal.ofReal Mc)
    (hMe : eLpNorm (fun ω : BilateralField d => aux_lem_15_u_supn Qt hQt (ω k0) ^ 2 *
        Real.exp (8 * aux_lem_15_u_supn Qt hQt (ω k0))) 1 (Measure.infinitePi μs) ≤
      ENNReal.ofReal Me) :
    eLpNorm (fun q : BilateralField d × BilateralField d =>
        RN q.1 - RN (Function.update q.1 k0 (q.2 k0)))
      (ENNReal.ofReal p) ((Measure.infinitePi μs).prod (Measure.infinitePi μs)) ≤
    ENNReal.ofReal (2 * (2 * Astrip * Mdel * B) +
      2 * (Cp * (Real.sqrt (8 * (2 * Acore + 4 * Astrip)) *
        ((Real.sqrt Me * Ma + Real.sqrt Mc * Mb) * (2 * B))))) := by
  haveI : IsProbabilityMeasure ((Measure.infinitePi μs).map (fun ω : BilateralField d => ω k0)) :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply k0).aemeasurable
  haveI : ∀ k, IsProbabilityMeasure (aux_lem_15_u_muk μs k0 a ell w idx k) := fun k => by
    unfold aux_lem_15_u_muk
    exact Measure.isProbabilityMeasure_map
      (aux_lem_15_u_localize_continuous a ell w (idx k)).measurable.aemeasurable
  have hp0 : 0 < p := by linarith
  have hRNeq : RN = fun ω => aux_lem_15_u_R S dir bd L
      (aux_lem_15_u_embU Qt hQt hQQt (base ω + ω k0)) := funext hRN
  have hRm : Measurable RN := by
    rw [hRNeq]
    exact ((aux_lem_15_u_resp_continuous S dir bd L).comp
      (aux_lem_15_u_emb_continuous Qt hQt hQQt Set.univ MeasurableSet.univ)).measurable.comp
      (hbase.add (measurable_pi_apply k0))
  have hΨm : Measurable (Function.uncurry
      (aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx)) :=
    (aux_lem_15_u_Psi_continuous S dir bd L Qt hQt hQQt a ell w idx).measurable
  have hTm : Measurable (fun ω : BilateralField d => fun k : Fin m =>
      aux_lem_15_u_localize a ell w (idx k) (ω k0)) :=
    measurable_pi_lambda _ fun k =>
      (aux_lem_15_u_localize_continuous a ell w (idx k)).measurable.comp (measurable_pi_apply k0)
  have hYm : Measurable (fun ω : BilateralField d =>
      aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx (base ω)
        (fun k => aux_lem_15_u_localize a ell w (idx k) (ω k0))) :=
    aux_lem_15_u_measurable_uncurry_comp _ hΨm _ _ hbase hTm
  have hGm : Measurable (fun f : C(SpatialCoordinates d, ℝ) =>
      ∫ v, aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx f v
        ∂(Measure.pi (aux_lem_15_u_muk μs k0 a ell w idx))) :=
    (hΨm.stronglyMeasurable.integral_prod_right
      (ν := Measure.pi (aux_lem_15_u_muk μs k0 a ell w idx))).measurable
  have hSm : Measurable (fun ω : BilateralField d => aux_lem_15_u_supn Qt hQt (ω k0)) :=
    (aux_lem_15_u_supn_continuous Qt hQt).measurable.comp (measurable_pi_apply k0)
  -- deletion term
  have h1 := aux_lem_15_u_deletion_Lp (Measure.infinitePi μs) p hp0
    (fun ω => RN ω - aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx (base ω)
        (fun k => aux_lem_15_u_localize a ell w (idx k) (ω k0)))
    (fun ω => aux_lem_15_u_supn Qt hQt (ω k0)) K hSm.aestronglyMeasurable hKm Astrip hAs
    (by
      filter_upwards [hgrowth] with ω hω
      obtain ⟨hK0, hg⟩ := hω
      have hd := aux_lem_15_u_diag S dir bd L Qt hQt hQQt a ell w hell hw hwl idx hinj hcover
        hkbox t Astrip Acore hSB hAs hAc (base ω) (ω k0) (K ω) hK0 hg
      rw [hRN ω]
      exact hd.1)
    (by filter_upwards [hgrowth] with ω hω; exact hω.1)
    (fun ω => aux_lem_15_u_supn_nonneg Qt hQt (ω k0)) Mdel B hMdel0 hMdel hmK
  -- centered deleted response
  have hmR' : eLpNorm (fun ω : BilateralField d =>
      aux_lem_15_u_R S dir bd L (aux_lem_15_u_embU Qt hQt hQQt (base ω + ω k0)))
      (ENNReal.ofReal (3 * p)) (Measure.infinitePi μs) ≤ ENNReal.ofReal B := by
    rw [← hRNeq]; exact hmR
  have h2 := aux_lem_15_u_es_term S dir bd L Qt hQt hQQt μs k0 base hbase hinv K hKm t hgrowth
    p B hp hB hmK hmR' a ell w hell hw hwl idx hinj hcover hkbox Astrip Acore hSB hAs hAc hπ
    Cp hCp hES Mexp Ma Mb Mc Me hMa0 hMb0 hMc0 hMe0 hMexp hMa hMb hMc hMe
  exact aux_lem_15_u_fourterm μs k0 base hbase hinv RN
    (fun ω => aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx (base ω)
        (fun k => aux_lem_15_u_localize a ell w (idx k) (ω k0)))
    (fun f => ∫ v, aux_lem_15_u_Psi S dir bd L Qt hQt hQQt a ell w idx f v
        ∂(Measure.pi (aux_lem_15_u_muk μs k0 a ell w idx)))
    hRm.aestronglyMeasurable hYm.aestronglyMeasurable hGm p hp _ _
    (by positivity) (by
      have : 0 ≤ Real.sqrt (8 * (2 * Acore + 4 * Astrip)) := Real.sqrt_nonneg _
      have : 0 ≤ Real.sqrt Me := Real.sqrt_nonneg _
      have : 0 ≤ Real.sqrt Mc := Real.sqrt_nonneg _
      positivity) h1 h2


variable {d : ℕ}

theorem aux_lem_15_u_exp_sub_one_le (x : ℝ) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-x)
  have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos x]

/-- Product functions of the two coordinates in `L^p` of the product law. -/
theorem aux_lem_15_u_prod_Lp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (q : ℝ) (hq : 0 < q) (A Bf : Ω → ℝ)
    (hA : AEStronglyMeasurable A P) (hBf : AEStronglyMeasurable Bf P) :
    eLpNorm (fun z : Ω × Ω => A z.1 * Bf z.2) (ENNReal.ofReal q) (P.prod P) ≤
      eLpNorm A (ENNReal.ofReal (2 * q)) P * eLpNorm Bf (ENNReal.ofReal (2 * q)) P := by
  have hf : MeasurePreserving (Prod.fst : Ω × Ω → Ω) (P.prod P) P := measurePreserving_fst
  have hs : MeasurePreserving (Prod.snd : Ω × Ω → Ω) (P.prod P) P := measurePreserving_snd
  have h := aux_lem_15_u_holder (hA.comp_measurePreserving hf) (hBf.comp_measurePreserving hs) hq
  rw [eLpNorm_comp_measurePreserving hA hf, eLpNorm_comp_measurePreserving hBf hs] at h
  exact h

theorem aux_lem_15_u_initial
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q) (dir : Bool)
    (bd : weakSobolevGraph Q) (L : S.space →L[ℝ] ℝ)
    (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt)
    (hQQt : (Q : Set (SpatialCoordinates d)) ⊆ Qt)
    (μs : ℤ → Measure C(SpatialCoordinates d, ℝ)) [∀ i, IsProbabilityMeasure (μs i)] (k0 : ℤ)
    (base : BilateralField d → C(SpatialCoordinates d, ℝ)) (hbase : Measurable base)
    (hinv : ∀ᵐ q ∂((Measure.infinitePi μs).prod (Measure.infinitePi μs)),
      base (Function.update q.1 k0 (q.2 k0)) = base q.1)
    (RN : BilateralField d → ℝ)
    (hRN : ∀ ω, RN ω = aux_lem_15_u_R S dir bd L (aux_lem_15_u_embU Qt hQt hQQt (base ω + ω k0)))
    (p B : ℝ) (hp : 1 ≤ p)
    (hmR : eLpNorm RN (ENNReal.ofReal (3 * p)) (Measure.infinitePi μs) ≤ ENNReal.ofReal B)
    (N1 N0 : ℝ) (hN1 : 0 ≤ N1) (hN0 : 0 ≤ N0)
    (hm1 : eLpNorm (fun ω : BilateralField d => aux_lem_15_u_supn Qt hQt (ω k0) *
        Real.exp (aux_lem_15_u_supn Qt hQt (ω k0))) (ENNReal.ofReal (4 * p))
      (Measure.infinitePi μs) ≤ ENNReal.ofReal N1)
    (hm0 : eLpNorm (fun ω : BilateralField d => Real.exp (aux_lem_15_u_supn Qt hQt (ω k0)))
      (ENNReal.ofReal (4 * p)) (Measure.infinitePi μs) ≤ ENNReal.ofReal N0) :
    eLpNorm (fun q : BilateralField d × BilateralField d =>
        RN q.1 - RN (Function.update q.1 k0 (q.2 k0)))
      (ENNReal.ofReal p) ((Measure.infinitePi μs).prod (Measure.infinitePi μs)) ≤
    ENNReal.ofReal (2 * (N1 * N0) * B) := by
  have hp0 : 0 < p := by linarith
  set P := Measure.infinitePi μs with hPdef
  have hRm : Measurable RN := by
    have hRNeq : RN = fun ω => aux_lem_15_u_R S dir bd L
        (aux_lem_15_u_embU Qt hQt hQQt (base ω + ω k0)) := funext hRN
    rw [hRNeq]
    exact ((aux_lem_15_u_resp_continuous S dir bd L).comp
      (aux_lem_15_u_emb_continuous Qt hQt hQQt Set.univ MeasurableSet.univ)).measurable.comp
      (hbase.add (measurable_pi_apply k0))
  have hSm : Measurable (fun ω : BilateralField d => aux_lem_15_u_supn Qt hQt (ω k0)) :=
    (aux_lem_15_u_supn_continuous Qt hQt).measurable.comp (measurable_pi_apply k0)
  set Sf : BilateralField d → ℝ := fun ω => aux_lem_15_u_supn Qt hQt (ω k0) with hSf
  have hSf0 : ∀ ω, 0 ≤ Sf ω := fun ω => aux_lem_15_u_supn_nonneg Qt hQt (ω k0)
  set Φ : BilateralField d × BilateralField d → ℝ := fun z =>
    Sf z.1 * Real.exp (Sf z.1) * Real.exp (Sf z.2) +
      Real.exp (Sf z.1) * (Sf z.2 * Real.exp (Sf z.2)) with hΦ
  have hpt : ∀ᵐ z ∂(P.prod P),
      ‖RN z.1 - RN (Function.update z.1 k0 (z.2 k0))‖ ≤ ‖Φ z * RN z.1‖ := by
    filter_upwards [hinv] with z hz
    rw [hRN z.1, hRN (Function.update z.1 k0 (z.2 k0)), hz, Function.update_self]
    set b := base z.1
    have hsub := aux_lem_15_u_resp_sub_le S dir bd L
      (aux_lem_15_u_embU Qt hQt hQQt (b + z.2 k0)) (aux_lem_15_u_embU Qt hQt hQQt (b + z.1 k0))
    have hdiff : aux_lem_15_u_embU Qt hQt hQQt (b + z.2 k0) -
        aux_lem_15_u_embU Qt hQt hQQt (b + z.1 k0) =
        aux_lem_15_u_embU Qt hQt hQQt (z.2 k0 - z.1 k0) := by
      unfold aux_lem_15_u_embU
      rw [← aux_lem_15_u_emb_sub]
      congr 1
      abel
    have hn : ‖aux_lem_15_u_embU Qt hQt hQQt (b + z.2 k0) -
        aux_lem_15_u_embU Qt hQt hQQt (b + z.1 k0)‖ ≤ Sf z.1 + Sf z.2 := by
      rw [hdiff]
      refine (aux_lem_15_u_emb_norm_le Qt hQt hQQt _ _ _).trans ?_
      have := aux_lem_15_u_supn_sub_le Qt hQt (z.2 k0) (z.1 k0)
      show aux_lem_15_u_supn Qt hQt (z.2 k0 - z.1 k0) ≤ _
      linarith
    have hR0 : 0 ≤ aux_lem_15_u_R S dir bd L (aux_lem_15_u_embU Qt hQt hQQt (b + z.1 k0)) :=
      aux_lem_15_u_resp_nonneg _ _ _ _ _
    have hx0 : 0 ≤ Sf z.1 + Sf z.2 := add_nonneg (hSf0 _) (hSf0 _)
    have hexp : Real.exp ‖aux_lem_15_u_embU Qt hQt hQQt (b + z.2 k0) -
        aux_lem_15_u_embU Qt hQt hQQt (b + z.1 k0)‖ - 1 ≤ Φ z := by
      have h1 := aux_lem_15_u_exp_sub_one_le ‖aux_lem_15_u_embU Qt hQt hQQt
        (b + z.2 k0) - aux_lem_15_u_embU Qt hQt hQQt (b + z.1 k0)‖
      have h2 := aux_lem_15_u_mono_mul_exp (norm_nonneg _) hn (zero_le_one' ℝ)
      have h3 : (Sf z.1 + Sf z.2) * Real.exp (1 * (Sf z.1 + Sf z.2)) = Φ z := by
        rw [hΦ, one_mul, Real.exp_add]; ring
      have h4 : ‖aux_lem_15_u_embU Qt hQt hQQt (b + z.2 k0) -
          aux_lem_15_u_embU Qt hQt hQQt (b + z.1 k0)‖ * Real.exp ‖aux_lem_15_u_embU Qt hQt hQQt
          (b + z.2 k0) - aux_lem_15_u_embU Qt hQt hQQt (b + z.1 k0)‖ =
          ‖aux_lem_15_u_embU Qt hQt hQQt (b + z.2 k0) -
          aux_lem_15_u_embU Qt hQt hQQt (b + z.1 k0)‖ * Real.exp (1 * ‖aux_lem_15_u_embU Qt hQt
          hQQt (b + z.2 k0) - aux_lem_15_u_embU Qt hQt hQQt (b + z.1 k0)‖) := by rw [one_mul]
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm]
    refine hsub.trans ?_
    rw [abs_mul, abs_of_nonneg hR0]
    exact mul_le_mul_of_nonneg_right (hexp.trans (le_abs_self _)) hR0
  have hΦm : AEStronglyMeasurable Φ (P.prod P) := by
    have h1 : Measurable (fun z : BilateralField d × BilateralField d => Sf z.1) :=
      hSm.comp measurable_fst
    have h2 : Measurable (fun z : BilateralField d × BilateralField d => Sf z.2) :=
      hSm.comp measurable_snd
    exact (((h1.mul (Real.continuous_exp.measurable.comp h1)).mul
      (Real.continuous_exp.measurable.comp h2)).add
      ((Real.continuous_exp.measurable.comp h1).mul
        (h2.mul (Real.continuous_exp.measurable.comp h2)))).aestronglyMeasurable
  have hRfst : AEStronglyMeasurable (fun z : BilateralField d × BilateralField d => RN z.1)
      (P.prod P) := (hRm.comp measurable_fst).aestronglyMeasurable
  have hH := aux_lem_15_u_holder hΦm hRfst hp0
  have hRfstn : eLpNorm (fun z : BilateralField d × BilateralField d => RN z.1)
      (ENNReal.ofReal (2 * p)) (P.prod P) ≤ ENNReal.ofReal B := by
    have := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal (2 * p)) hRm.aestronglyMeasurable
      (measurePreserving_fst (μ := P) (ν := P))
    simp only [Function.comp_def] at this
    rw [this]
    exact (aux_lem_15_u_exponent_mono hRm.aestronglyMeasurable (by linarith)).trans hmR
  have hSe : AEStronglyMeasurable (fun ω : BilateralField d => Sf ω * Real.exp (Sf ω)) P :=
    (hSm.mul (Real.continuous_exp.measurable.comp hSm)).aestronglyMeasurable
  have hE : AEStronglyMeasurable (fun ω : BilateralField d => Real.exp (Sf ω)) P :=
    (Real.continuous_exp.measurable.comp hSm).aestronglyMeasurable
  have hΦn : eLpNorm Φ (ENNReal.ofReal (2 * p)) (P.prod P) ≤ ENNReal.ofReal (2 * (N1 * N0)) := by
    have h2p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * p) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
    have hA := aux_lem_15_u_prod_Lp P (2 * p) (by linarith) _ _ hSe hE
    have hB' := aux_lem_15_u_prod_Lp P (2 * p) (by linarith) _ _ hE hSe
    have e4 : 2 * (2 * p) = 4 * p := by ring
    rw [e4] at hA hB'
    have hsplit := eLpNorm_add_le
      (f := fun z : BilateralField d × BilateralField d => Sf z.1 * Real.exp (Sf z.1) *
        Real.exp (Sf z.2))
      (g := fun z : BilateralField d × BilateralField d => Real.exp (Sf z.1) *
        (Sf z.2 * Real.exp (Sf z.2)))
      (hSe.comp_measurePreserving measurePreserving_fst |>.mul
        (hE.comp_measurePreserving measurePreserving_snd))
      (hE.comp_measurePreserving measurePreserving_fst |>.mul
        (hSe.comp_measurePreserving measurePreserving_snd)) h2p
    refine hsplit.trans ?_
    calc eLpNorm (fun z : BilateralField d × BilateralField d => Sf z.1 * Real.exp (Sf z.1) *
          Real.exp (Sf z.2)) (ENNReal.ofReal (2 * p)) (P.prod P) +
        eLpNorm (fun z : BilateralField d × BilateralField d => Real.exp (Sf z.1) *
          (Sf z.2 * Real.exp (Sf z.2))) (ENNReal.ofReal (2 * p)) (P.prod P)
        ≤ ENNReal.ofReal N1 * ENNReal.ofReal N0 + ENNReal.ofReal N0 * ENNReal.ofReal N1 := by
          gcongr
          · exact hA.trans (mul_le_mul' hm1 hm0)
          · exact hB'.trans (mul_le_mul' hm0 hm1)
      _ = ENNReal.ofReal (2 * (N1 * N0)) := by
          rw [← ENNReal.ofReal_mul hN1, ← ENNReal.ofReal_mul hN0,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  calc eLpNorm (fun q : BilateralField d × BilateralField d =>
        RN q.1 - RN (Function.update q.1 k0 (q.2 k0))) (ENNReal.ofReal p) (P.prod P)
      ≤ eLpNorm (fun z => Φ z * RN z.1) (ENNReal.ofReal p) (P.prod P) := eLpNorm_mono_ae hpt
    _ ≤ eLpNorm Φ (ENNReal.ofReal (2 * p)) (P.prod P) *
        eLpNorm (fun z : BilateralField d × BilateralField d => RN z.1)
          (ENNReal.ofReal (2 * p)) (P.prod P) := hH
    _ ≤ ENNReal.ofReal (2 * (N1 * N0)) * ENNReal.ofReal B := mul_le_mul' hΦn hRfstn
    _ = ENNReal.ofReal (2 * (N1 * N0) * B) := by
        rw [← ENNReal.ofReal_mul (by positivity)]


theorem aux_lem_15_u_env
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) (dir : Bool)
    (bd : weakSobolevGraph (centeredCube z r hr)) (L : S.space →L[ℝ] ℝ)
    (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt)
    (hQQt : ((centeredCube z r hr : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) ⊆ Qt)
    (t : ℝ) (delta : ℝ) (hdelta : 0 < delta) (hdelta_le : delta ≤ 1)
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (hG1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
    (hG2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHmeas : Measurable H)
    (hHconv : ∀ᵐ omega ∂((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure),
      Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)))
    (kappa : ℕ → ℝ)
    (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr))
    (haN : ∀ N omega,
      (aN N omega).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N))))
    (K : ℕ → BilateralField d → ℝ)
    (hK : ∀ᵐ omega ∂((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure),
      ∀ N, 0 ≤ K N omega)
    (hgrowth : ∀ᵐ omega ∂((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure),
      ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
          localGradientEnergy (aN N omega)
            (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
            (aux_lem_15_u_grad S dir bd L (aN N omega)) ≤ K N omega * rho ^ t)
    (N j : ℕ) (hjN : j ≤ N) :
    let μs : ℤ → Measure C(SpatialCoordinates d, ℝ) := fun i =>
      (scaledLayerLaw d ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable) i :
        Measure C(SpatialCoordinates d, ℝ))
    let base := aux_lem_15_u_base H N j (Real.log (kappa N))
    Measurable base ∧
    (∀ᵐ q ∂((Measure.infinitePi μs).prod (Measure.infinitePi μs)),
      base (Function.update q.1 (-(j : ℤ)) (q.2 (-(j : ℤ)))) = base q.1) ∧
    (∀ omega, aN N omega = expPotentialCoefficient
      (aux_lem_15_u_embU Qt hQt hQQt (base omega + omega (-(j : ℤ))))) ∧
    (∀ᵐ omega ∂(Measure.infinitePi μs), 0 ≤ K N omega ∧
      aux_lem_15_u_Growth S dir bd L t
        (aux_lem_15_u_embU Qt hQt hQQt (base omega + omega (-(j : ℤ)))) (K N omega)) := by
  intro μs base
  have hcoef : ∀ omega, aN N omega = expPotentialCoefficient
      (aux_lem_15_u_embU Qt hQt hQQt (base omega + omega (-(j : ℤ)))) :=
    fun omega => aux_lem_15_u_coeff_eq Qt hQt hQQt H N j hjN (kappa N) omega (aN N omega)
      (haN N omega)
  refine ⟨aux_lem_15_u_base_measurable H hHmeas N j _, ?_, hcoef, ?_⟩
  · have hHinv := aux_lem_15_update_H_ae d hd delta hdelta hdelta_le Praw hG1 hG2 H hHmeas
      hHconv j
    simp only at hHinv
    filter_upwards [hHinv] with q hq
    exact aux_lem_15_u_base_update H N j _ q.1 (q.2 (-(j : ℤ))) hq.symm
  · have hK' : ∀ᵐ omega ∂(Measure.infinitePi μs), ∀ N, 0 ≤ K N omega := hK
    have hg' : ∀ᵐ omega ∂(Measure.infinitePi μs), ∀ N, ∀ x ∈ (centeredCube z r hr : Set _),
        ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
          localGradientEnergy (aN N omega) (s := Metric.ball x rho)
            Metric.isOpen_ball.measurableSet
            (aux_lem_15_u_grad S dir bd L (aN N omega)) ≤ K N omega * rho ^ t := hgrowth
    filter_upwards [hK', hg'] with omega h1 h2
    refine ⟨h1 N, ?_⟩
    intro x hx rho hrho hrho1
    have h := h2 N x hx rho hrho hrho1
    rw [hcoef omega] at h
    exact h

/-! ## Numerical bookkeeping -/



theorem aux_lem_15_u_exponent (a : ℝ) (ha : 0 ≤ a) (j : ℕ) :
    (3 : ℝ) ^ (-(3 * a / 8) * (j : ℝ)) ≤
      (3 : ℝ) ^ (-(a / (8 * Real.log 3)) * (j : ℝ)) := by
  have hlog : (1 / 3 : ℝ) ≤ Real.log 3 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 by norm_num)
    norm_num at h ⊢
    linarith
  have hlogpos : 0 < Real.log 3 := lt_of_lt_of_le (by norm_num) hlog
  have hinv : 1 / Real.log 3 ≤ (3 : ℝ) := by
    apply (div_le_iff₀ hlogpos).2
    nlinarith
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hcoef : a / (8 * Real.log 3) ≤ 3 * a / 8 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * Real.log 3)).2
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hinv)]
  nlinarith [mul_nonneg hj (sub_nonneg.mpr hcoef)]

/-- Masking-case constant bookkeeping in terms of `v = r^{b/2}` and `u = r^{-γ/2}`. -/
theorem aux_lem_15_u_mask_numeric (δ B Cd cR Cdel Ca Cb Cc Ce Cp v u : ℝ) (hδ : 0 ≤ δ)
    (hB : 0 ≤ B) (hCd : 0 ≤ Cd) (hcR : 0 ≤ cR) (hCdel : 0 ≤ Cdel)
    (hCc : 0 ≤ Cc) (hCe : 0 ≤ Ce) (hv : 0 ≤ v) (hu : 0 ≤ u)
    (hvu : v ^ 2 * u ^ 2 ≤ v * u ^ 3) :
    2 * (2 * (Cd * cR * v ^ 2) * (Cdel * δ * u ^ 2) * B) +
      2 * (Cp * (Real.sqrt (8 * (2 * (Cd * v ^ 2) + 4 * (Cd * cR * v ^ 2))) *
        ((Real.sqrt (Ce * δ ^ 2 * u ^ 2) * (Ca * u ^ 2) +
          Real.sqrt (Cc * u ^ 2) * (Cb * δ * u ^ 2)) * (2 * B)))) ≤
    (4 * Cd * cR * Cdel * B +
      4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * cR)) * (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) *
      δ * (v * u ^ 3) := by
  have h1 : Real.sqrt (8 * (2 * (Cd * v ^ 2) + 4 * (Cd * cR * v ^ 2))) =
      Real.sqrt (8 * Cd * (2 + 4 * cR)) * v := by
    rw [show 8 * (2 * (Cd * v ^ 2) + 4 * (Cd * cR * v ^ 2)) = 8 * Cd * (2 + 4 * cR) * v ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hv]
  have h2 : Real.sqrt (Ce * δ ^ 2 * u ^ 2) = Real.sqrt Ce * δ * u := by
    rw [show Ce * δ ^ 2 * u ^ 2 = Ce * (δ * u) ^ 2 by ring, Real.sqrt_mul hCe,
      Real.sqrt_sq (by positivity)]
    ring
  have h3 : Real.sqrt (Cc * u ^ 2) = Real.sqrt Cc * u := by
    rw [Real.sqrt_mul hCc, Real.sqrt_sq hu]
  rw [h1, h2, h3]
  have hdel : 2 * (2 * (Cd * cR * v ^ 2) * (Cdel * δ * u ^ 2) * B) ≤
      4 * Cd * cR * Cdel * B * δ * (v * u ^ 3) := by
    have hc : 0 ≤ 4 * Cd * cR * Cdel * B * δ := by positivity
    calc 2 * (2 * (Cd * cR * v ^ 2) * (Cdel * δ * u ^ 2) * B)
        = 4 * Cd * cR * Cdel * B * δ * (v ^ 2 * u ^ 2) := by ring
      _ ≤ 4 * Cd * cR * Cdel * B * δ * (v * u ^ 3) := mul_le_mul_of_nonneg_left hvu hc
  have hes : 2 * (Cp * (Real.sqrt (8 * Cd * (2 + 4 * cR)) * v *
        ((Real.sqrt Ce * δ * u * (Ca * u ^ 2) + Real.sqrt Cc * u * (Cb * δ * u ^ 2)) * (2 * B)))) =
      4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * cR)) * (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B *
        δ * (v * u ^ 3) := by ring
  rw [hes]
  nlinarith [hdel]


variable {d : ℕ}

/-- The enlarged closed cube carrying all clamping boxes and the layer sup norm. -/
def aux_lem_15_u_Qt (z : SpatialCoordinates d) (r : ℝ) : Set (SpatialCoordinates d) :=
  Metric.closedBall z (r / 2 + 1)

theorem aux_lem_15_u_Qt_compact (z : SpatialCoordinates d) (r : ℝ) :
    IsCompact (aux_lem_15_u_Qt z r) := isCompact_closedBall _ _

theorem aux_lem_15_u_Qt_nonempty (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    (aux_lem_15_u_Qt z r).Nonempty := ⟨z, Metric.mem_closedBall_self (by linarith)⟩

theorem aux_lem_15_u_Qt_sub (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ((centeredCube z r hr : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) ⊆
      aux_lem_15_u_Qt z r :=
  Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))

theorem aux_lem_15_u_Qt_bound (z : SpatialCoordinates d) (r : ℝ) :
    ∀ x ∈ aux_lem_15_u_Qt z r, ∀ i, |x i| ≤ ‖z‖ + (r / 2 + 1) := by
  intro x hx i
  have h1 : ‖x‖ ≤ ‖z‖ + (r / 2 + 1) := by
    have := norm_le_norm_add_norm_sub' x z
    have h2 : ‖x - z‖ ≤ r / 2 + 1 := by
      rw [← dist_eq_norm]; exact hx
    linarith
  exact (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i : |x i| ≤ ‖x‖).trans h1

/-- `lem_strips` in the form used by the masking step, with the constant `Cd` chosen
before the exponent `t`, and `r0` after `t` only. -/
theorem aux_lem_15_u_geom (d : ℕ) (hd : 1 ≤ d) (Cs : ℝ) (hCs : 0 < Cs) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ (t : ℝ), (d : ℝ) - 1 < t →
      0 < t * (t - (d : ℝ) + 1) / (t + 1) ∧
      ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ 1 ∧
        ∀ (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (rs : ℝ), 0 < rs → rs ≤ r0 →
          (0 < rs ^ ((t - (d : ℝ) + 1) / (t + 1)) ∧ rs ^ ((t - (d : ℝ) + 1) / (t + 1)) ≤ 1 ∧
            Cs * rs < rs ^ ((t - (d : ℝ) + 1) / (t + 1))) ∧
          aux_lem_15_u_StripBound (centeredCube z R hR) t 0
            (rs ^ ((t - (d : ℝ) + 1) / (t + 1))) (Cs * rs)
            (Cd * (max 1 R) ^ d * rs ^ (t * (t - (d : ℝ) + 1) / (t + 1)))
            (Cd * rs ^ (t * (t - (d : ℝ) + 1) / (t + 1))) := by
  have h := lem_strips d hd Cs hCs
  rcases h with ⟨Cd, hCd, h⟩
  refine ⟨Cd, hCd, fun t ht => ?_⟩
  have h2 := h t ht
  dsimp only at h2
  rcases h2 with ⟨hb, r0, hr0, hr01, hRall⟩
  refine ⟨hb, r0, hr0, hr01, fun z R hR rs hrs hrs0 => ⟨?_, ?_⟩⟩
  · have h3 := hRall z R hR 0 (0 : Measure (SpatialCoordinates d)) 0 le_rfl
      (by intro x _ rad _ _; simp)
    rcases h3 with ⟨_, hB, _⟩
    rcases hB rs hrs hrs0 with ⟨h1, h2, h3, _, _⟩
    exact ⟨h1, h2, h3⟩
  · intro nu hfin Kv hKv hν
    have h3 := hRall z R hR 0 nu Kv hKv hν
    rcases h3 with ⟨_, hB, _⟩
    rcases hB rs hrs hrs0 with ⟨_, _, _, hstr, hmax⟩
    constructor
    · refine hstr.trans (le_of_eq ?_)
      congr 1; ring
    · intro idx
      refine (le_iSup (fun idx : Fin d → ℤ => nu ((centeredCube z R hR : Set (SpatialCoordinates d)) ∩
        {x | ∀ i : Fin d, (0 : SpatialCoordinates d) i + (idx i : ℝ) *
          rs ^ ((t - (d : ℝ) + 1) / (t + 1)) ≤ x i ∧
          x i < (0 : SpatialCoordinates d) i + ((idx i : ℝ) + 1) *
            rs ^ ((t - (d : ℝ) + 1) / (t + 1))})) idx).trans (hmax.trans (le_of_eq ?_))
      congr 1; ring

/-- The layer-moment bound in the `supn` form. -/
theorem aux_lem_15_u_moment_supn [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt) (P : Measure (BilateralField d))
    (j : ℕ) (p' lam c : ℝ) (n : ℕ)
    (h : eLpNorm (fun ω : BilateralField d =>
        (sSup ((fun x : SpatialCoordinates d => ‖ω (-(j : ℤ)) x‖) '' Qt)) ^ ((n : ℕ) : ℝ) *
          Real.exp (lam * sSup ((fun x : SpatialCoordinates d => ‖ω (-(j : ℤ)) x‖) '' Qt)))
      (ENNReal.ofReal p') P ≤ ENNReal.ofReal c) :
    eLpNorm (fun ω : BilateralField d => aux_lem_15_u_supn Qt hQt (ω (-(j : ℤ))) ^ n *
        Real.exp (lam * aux_lem_15_u_supn Qt hQt (ω (-(j : ℤ))))) (ENNReal.ofReal p') P ≤
      ENNReal.ofReal c := by
  have e : (fun ω : BilateralField d => aux_lem_15_u_supn Qt hQt (ω (-(j : ℤ))) ^ n *
        Real.exp (lam * aux_lem_15_u_supn Qt hQt (ω (-(j : ℤ))))) =
      (fun ω : BilateralField d =>
        (sSup ((fun x : SpatialCoordinates d => ‖ω (-(j : ℤ)) x‖) '' Qt)) ^ ((n : ℕ) : ℝ) *
          Real.exp (lam * sSup ((fun x : SpatialCoordinates d => ‖ω (-(j : ℤ)) x‖) '' Qt))) := by
    funext ω
    rw [aux_lem_15_u_supn_eq_sSup, Real.rpow_natCast]
  rw [e]; exact h

/-- `r^{-γ}` and `r^{b}` for `r = 3^{-j}` in the `u, v` form. -/
theorem aux_lem_15_u_rpow_facts (rs bexp : ℝ) (hrs : 0 < rs) (hrs1 : rs ≤ 1) (hb : 0 < bexp) :
    rs ^ bexp = (rs ^ (bexp / 2)) ^ 2 ∧ rs ^ (-(bexp / 12)) = (rs ^ (-(bexp / 12) / 2)) ^ 2 ∧
      rs ^ (3 * bexp / 8) = rs ^ (bexp / 2) * (rs ^ (-(bexp / 12) / 2)) ^ 3 ∧
      (rs ^ (bexp / 2)) ^ 2 * (rs ^ (-(bexp / 12) / 2)) ^ 2 ≤
        rs ^ (bexp / 2) * (rs ^ (-(bexp / 12) / 2)) ^ 3 := by
  have hpow : ∀ (x : ℝ) (n : ℕ), (rs ^ x) ^ n = rs ^ (x * n) := by
    intro x n
    rw [← Real.rpow_natCast, ← Real.rpow_mul hrs.le]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hpow]; congr 1; push_cast; ring
  · rw [hpow]; congr 1; push_cast; ring
  · rw [hpow, ← Real.rpow_add hrs]; congr 1; push_cast; ring
  · have hv0 : 0 ≤ rs ^ (bexp / 2) := (Real.rpow_pos_of_pos hrs _).le
    have hu0 : 0 ≤ rs ^ (-(bexp / 12) / 2) := (Real.rpow_pos_of_pos hrs _).le
    have hvu : rs ^ (bexp / 2) ≤ rs ^ (-(bexp / 12) / 2) :=
      Real.rpow_le_rpow_of_exponent_ge hrs hrs1 (by linarith)
    have hc : 0 ≤ rs ^ (bexp / 2) * (rs ^ (-(bexp / 12) / 2)) ^ 2 := by positivity
    calc (rs ^ (bexp / 2)) ^ 2 * (rs ^ (-(bexp / 12) / 2)) ^ 2
        = (rs ^ (bexp / 2) * (rs ^ (-(bexp / 12) / 2)) ^ 2) * rs ^ (bexp / 2) := by ring
      _ ≤ (rs ^ (bexp / 2) * (rs ^ (-(bexp / 12) / 2)) ^ 2) * rs ^ (-(bexp / 12) / 2) :=
          mul_le_mul_of_nonneg_left hvu hc
      _ = rs ^ (bexp / 2) * (rs ^ (-(bexp / 12) / 2)) ^ 3 := by ring


/-- The masking case `3^{-j} ≤ r_0` on the frozen data. -/
theorem aux_lem_15_u_mask_case
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) (dir : Bool)
    (bd : weakSobolevGraph (centeredCube z r hr)) (L : S.space →L[ℝ] ℝ)
    (t p B : ℝ) (hp : 2 ≤ p) (hB : 0 ≤ B)
    (Cd : ℝ) (hCd : 0 < Cd) (hbpos : 0 < t * (t - (d : ℝ) + 1) / (t + 1))
    (Cp : ℝ) (hCp : 0 < Cp)
    (hCpall : ∀ (m : ℕ) (mu : Fin m → Measure C(SpatialCoordinates d, ℝ))
      [∀ i, IsProbabilityMeasure (mu i)], aux_lem_15_u_ESProp mu p Cp)
    (Cexp Cdel Ca Cb Cc Ce : ℝ) (hCdel : 0 ≤ Cdel) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (hCc : 0 ≤ Cc) (hCe : 0 ≤ Ce)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta_le : delta ≤ 1)
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (hG1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
    (hG2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHmeas : Measurable H)
    (hHconv : ∀ᵐ omega ∂((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure),
      Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)))
    (kappa : ℕ → ℝ)
    (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr))
    (haN : ∀ N omega,
      (aN N omega).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N))))
    (K : ℕ → BilateralField d → ℝ)
    (hKm : ∀ N, AEStronglyMeasurable (K N) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure))
    (hK : ∀ᵐ omega ∂((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure),
      ∀ N, 0 ≤ K N omega)
    (hgrowth : ∀ᵐ omega ∂((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure),
      ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
          localGradientEnergy (aN N omega)
            (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
            (aux_lem_15_u_grad S dir bd L (aN N omega)) ≤ K N omega * rho ^ t)
    (N j : ℕ) (hjN : j ≤ N)
    (hmomK : eLpNorm (K N) (ENNReal.ofReal (3 * p)) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure) ≤
      ENNReal.ofReal B)
    (hmomR : eLpNorm (fun omega => aux_lem_15_u_resp S dir bd L (aN N omega))
      (ENNReal.ofReal (3 * p)) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure) ≤
      ENNReal.ofReal B)
    (rs : ℝ) (hrsdef : rs = (3 : ℝ) ^ (-(j : ℝ)))
    (hgeom : (0 < rs ^ ((t - (d : ℝ) + 1) / (t + 1)) ∧ rs ^ ((t - (d : ℝ) + 1) / (t + 1)) ≤ 1 ∧
        (2 * Real.sqrt d) * rs < rs ^ ((t - (d : ℝ) + 1) / (t + 1))) ∧
      aux_lem_15_u_StripBound (centeredCube z r hr) t 0
        (rs ^ ((t - (d : ℝ) + 1) / (t + 1))) ((2 * Real.sqrt d) * rs)
        (Cd * (max 1 r) ^ d * rs ^ (t * (t - (d : ℝ) + 1) / (t + 1)))
        (Cd * rs ^ (t * (t - (d : ℝ) + 1) / (t + 1))))
    (hMexp : eLpNorm (fun ω : BilateralField d => Real.exp (2 * aux_lem_15_u_supn
        (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ)))))
      (ENNReal.ofReal p) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure) ≤
      ENNReal.ofReal Cexp)
    (hMdel : eLpNorm (fun ω : BilateralField d => aux_lem_15_u_supn (aux_lem_15_u_Qt z r)
        (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ))) * Real.exp (4 * aux_lem_15_u_supn
        (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ)))))
      (ENNReal.ofReal (2 * p)) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure) ≤
      ENNReal.ofReal (Cdel * delta * rs ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 12))))
    (hMa : eLpNorm (fun ω : BilateralField d => Real.exp (7 * aux_lem_15_u_supn
        (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ)))))
      (ENNReal.ofReal (2 * p)) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure) ≤
      ENNReal.ofReal (Ca * rs ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 12))))
    (hMb : eLpNorm (fun ω : BilateralField d => aux_lem_15_u_supn (aux_lem_15_u_Qt z r)
        (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ))) * Real.exp (7 * aux_lem_15_u_supn
        (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ)))))
      (ENNReal.ofReal (2 * p)) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure) ≤
      ENNReal.ofReal (Cb * delta * rs ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 12))))
    (hMc : eLpNorm (fun ω : BilateralField d => Real.exp (8 * aux_lem_15_u_supn
        (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ))))) 1
      ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure) ≤
      ENNReal.ofReal (Cc * rs ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 12))))
    (hMe : eLpNorm (fun ω : BilateralField d => aux_lem_15_u_supn (aux_lem_15_u_Qt z r)
        (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ))) ^ 2 * Real.exp (8 * aux_lem_15_u_supn
        (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ))))) 1
      ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure) ≤
      ENNReal.ofReal (Ce * delta ^ 2 * rs ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 12)))) :
    eLpNorm (fun pair : BilateralField d × BilateralField d =>
        aux_lem_15_u_resp S dir bd L (aN N pair.1) -
          aux_lem_15_u_resp S dir bd L
            (aN N (Function.update pair.1 (-(j : ℤ)) (pair.2 (-(j : ℤ))))))
      (ENNReal.ofReal p)
      (((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure).prod
      ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure)) ≤
    ENNReal.ofReal ((4 * Cd * (max 1 r) ^ d * Cdel * B +
      4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
        (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) *
      delta * rs ^ (3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8)) := by
  -- environment
  set bexp := t * (t - (d : ℝ) + 1) / (t + 1) with hbexp
  set ell := rs ^ ((t - (d : ℝ) + 1) / (t + 1)) with hell_def
  set w := (2 * Real.sqrt d) * rs with hw_def
  have hrs : 0 < rs := by rw [hrsdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hrs1 : rs ≤ 1 := by
    rw [hrsdef]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith)
  obtain ⟨⟨hell, hell1, hwl⟩, hSB⟩ := hgeom
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d by omega))
  have hw : 0 < w := by rw [hw_def]; positivity
  have henv := aux_lem_15_u_env d hd z r hr S dir bd L (aux_lem_15_u_Qt z r)
    (aux_lem_15_u_Qt_compact z r) (aux_lem_15_u_Qt_sub z hr) t delta hdelta hdelta_le Praw hG1
    hG2 H hHmeas hHconv kappa aN haN K hK hgrowth N j hjN
  simp only at henv
  obtain ⟨hbase, hinv, hcoef, hgr⟩ := henv
  -- index set of the grid
  set I := aux_lem_15_u_index 0 z r ell with hI
  set idx : Fin I.card → (Fin d → ℤ) := fun k => (I.equivFin.symm k).1 with hidx
  have hinj : Function.Injective idx := by
    intro k k' h
    exact I.equivFin.symm.injective (Subtype.ext h)
  have hcover : ∀ x ∈ ((centeredCube z r hr : Opens (SpatialCoordinates d)) :
      Set (SpatialCoordinates d)), x ∉ aux_lem_15_u_stripSet 0 ell w →
      ∃ k, x ∈ aux_lem_15_u_core 0 ell w (idx k) := by
    intro x hx hxs
    have hmem := aux_lem_15_u_floorIdx_mem_index 0 z (s := r) hell hx
    refine ⟨I.equivFin ⟨_, hmem⟩, ?_⟩
    have : idx (I.equivFin ⟨_, hmem⟩) = aux_lem_15_u_floorIdx 0 ell x := by
      simp [hidx]
    rw [this]
    exact aux_lem_15_u_mem_core_of_not_strip 0 hell hxs
  have hkbox : ∀ k, aux_lem_15_u_kbox 0 ell w (idx k) ⊆ aux_lem_15_u_Qt z r := fun k =>
    aux_lem_15_u_kbox_subset 0 z hr.le hell hell1 hw.le (I.equivFin.symm k).2
  -- independence of the pieces
  have hsep : Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (-(-(j : ℤ))) * (w / 2) := by
    have h3 : (3 : ℝ) ^ (-(-(j : ℤ))) * rs = 1 := by
      rw [neg_neg, zpow_natCast, hrsdef, Real.rpow_neg (by norm_num), Real.rpow_natCast,
        mul_inv_cancel₀ (by positivity)]
    have : (3 : ℝ) ^ (-(-(j : ℤ))) * (w / 2) = Real.sqrt d * ((3 : ℝ) ^ (-(-(j : ℤ))) * rs) := by
      rw [hw_def]; ring
    rw [this, h3, mul_one]
  have hπ := aux_lem_15_u_key_law hd Praw hG1 j 0 hell.le hw hwl.le hsep idx hinj
  simp only at hπ
  haveI : IsProbabilityMeasure ((Measure.infinitePi (fun i => (scaledLayerLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable) i :
        Measure C(SpatialCoordinates d, ℝ)))).map (fun ω : BilateralField d => ω (-(j : ℤ)))) :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply _).aemeasurable
  haveI hprobk : ∀ k, IsProbabilityMeasure (aux_lem_15_u_muk (fun i => (scaledLayerLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable) i :
        Measure C(SpatialCoordinates d, ℝ))) (-(j : ℤ)) 0 ell w idx k) := fun k => by
    unfold aux_lem_15_u_muk
    exact Measure.isProbabilityMeasure_map
      (aux_lem_15_u_localize_continuous 0 ell w (idx k)).measurable.aemeasurable
  have hES := hCpall I.card (aux_lem_15_u_muk (fun i => (scaledLayerLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable) i :
        Measure C(SpatialCoordinates d, ℝ))) (-(j : ℤ)) 0 ell w idx)
  have hRN : ∀ ω, aux_lem_15_u_resp S dir bd L (aN N ω) = aux_lem_15_u_R S dir bd L
      (aux_lem_15_u_embU (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
        (aux_lem_15_u_Qt_sub z hr) (aux_lem_15_u_base H N j (Real.log (kappa N)) ω +
          ω (-(j : ℤ)))) := by
    intro ω; rw [hcoef ω]; rfl
  have hmain := aux_lem_15_u_masking S dir bd L (aux_lem_15_u_Qt z r)
    (aux_lem_15_u_Qt_compact z r) (aux_lem_15_u_Qt_sub z hr) _ (-(j : ℤ)) _ hbase hinv
    (fun ω => aux_lem_15_u_resp S dir bd L (aN N ω)) (K N) hRN (hKm N) t hgr p B
    (by linarith) hB hmomK hmomR 0 ell w hell hw hwl.le idx hinj hcover hkbox _ _ hSB
    (by positivity) (by positivity) hπ Cp hCp.le hES Cexp
    (Cdel * delta * rs ^ (-(bexp / 12))) (Ca * rs ^ (-(bexp / 12)))
    (Cb * delta * rs ^ (-(bexp / 12))) (Cc * rs ^ (-(bexp / 12)))
    (Ce * delta ^ 2 * rs ^ (-(bexp / 12)))
    (by have := Real.rpow_pos_of_pos hrs (-(bexp / 12)); positivity)
    (by have := Real.rpow_pos_of_pos hrs (-(bexp / 12)); positivity)
    (by have := Real.rpow_pos_of_pos hrs (-(bexp / 12)); positivity)
    (by have := Real.rpow_pos_of_pos hrs (-(bexp / 12)); positivity)
    (by have := Real.rpow_pos_of_pos hrs (-(bexp / 12)); positivity)
    hMexp hMdel hMa hMb hMc hMe
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  -- numerical bookkeeping
  obtain ⟨e1, e2, e3, hvu⟩ := aux_lem_15_u_rpow_facts rs bexp hrs hrs1 hbpos
  have hγ : -(t * (t - (d : ℝ) + 1) / (t + 1) / 12) = -(bexp / 12) := by rw [hbexp]
  rw [hγ, e1, e2, e3]
  exact aux_lem_15_u_mask_numeric delta B Cd ((max 1 r) ^ d) Cdel Ca Cb Cc Ce Cp
    (rs ^ (bexp / 2)) (rs ^ (-(bexp / 12) / 2)) hdelta.le hB hCd.le (by positivity) hCdel
    hCc hCe (Real.rpow_pos_of_pos hrs _).le (Real.rpow_pos_of_pos hrs _).le hvu


open scoped ContDiff

/-- The initial-scale case on the frozen data. -/
theorem aux_lem_15_u_init_case
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) (dir : Bool)
    (bd : weakSobolevGraph (centeredCube z r hr)) (L : S.space →L[ℝ] ℝ)
    (t p B : ℝ) (hp : 2 ≤ p)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta_le : delta ≤ 1)
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (hG1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
    (hG2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHmeas : Measurable H)
    (hHconv : ∀ᵐ omega ∂((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure),
      Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)))
    (kappa : ℕ → ℝ)
    (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr))
    (haN : ∀ N omega,
      (aN N omega).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N))))
    (K : ℕ → BilateralField d → ℝ)
    (hK : ∀ᵐ omega ∂((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure),
      ∀ N, 0 ≤ K N omega)
    (hgrowth : ∀ᵐ omega ∂((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure),
      ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
          localGradientEnergy (aN N omega)
            (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
            (aux_lem_15_u_grad S dir bd L (aN N omega)) ≤ K N omega * rho ^ t)
    (N j : ℕ) (hjN : j ≤ N)
    (hmomR : eLpNorm (fun omega => aux_lem_15_u_resp S dir bd L (aN N omega))
      (ENNReal.ofReal (3 * p)) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure) ≤
      ENNReal.ofReal B)
    (N1 N0 : ℝ) (hN1 : 0 ≤ N1) (hN0 : 0 ≤ N0)
    (hm1 : eLpNorm (fun om : BilateralField d => aux_lem_15_u_supn (aux_lem_15_u_Qt z r)
        (aux_lem_15_u_Qt_compact z r) (om (-(j : ℤ))) * Real.exp (aux_lem_15_u_supn
        (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r) (om (-(j : ℤ)))))
      (ENNReal.ofReal (4 * p)) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure) ≤
      ENNReal.ofReal N1)
    (hm0 : eLpNorm (fun om : BilateralField d => Real.exp (aux_lem_15_u_supn
        (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r) (om (-(j : ℤ)))))
      (ENNReal.ofReal (4 * p)) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure) ≤
      ENNReal.ofReal N0) :
    eLpNorm (fun pair : BilateralField d × BilateralField d =>
        aux_lem_15_u_resp S dir bd L (aN N pair.1) -
          aux_lem_15_u_resp S dir bd L
            (aN N (Function.update pair.1 (-(j : ℤ)) (pair.2 (-(j : ℤ))))))
      (ENNReal.ofReal p)
      (((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure).prod
      ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure)) ≤
    ENNReal.ofReal (2 * (N1 * N0) * B) := by
  have henv := aux_lem_15_u_env d hd z r hr S dir bd L (aux_lem_15_u_Qt z r)
    (aux_lem_15_u_Qt_compact z r) (aux_lem_15_u_Qt_sub z hr) t delta hdelta hdelta_le Praw hG1
    hG2 H hHmeas hHconv kappa aN haN K hK hgrowth N j hjN
  simp only at henv
  obtain ⟨hbase, hinv, hcoef, _⟩ := henv
  have hRN : ∀ om, aux_lem_15_u_resp S dir bd L (aN N om) = aux_lem_15_u_R S dir bd L
      (aux_lem_15_u_embU (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
        (aux_lem_15_u_Qt_sub z hr) (aux_lem_15_u_base H N j (Real.log (kappa N)) om +
          om (-(j : ℤ)))) := by
    intro om; rw [hcoef om]; rfl
  exact aux_lem_15_u_initial S dir bd L (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    (aux_lem_15_u_Qt_sub z hr) _ (-(j : ℤ)) _ hbase hinv
    (fun om => aux_lem_15_u_resp S dir bd L (aN N om)) hRN p B (by linarith) hmomR N1 N0 hN1 hN0
    hm1 hm0

/-- Real bookkeeping for the initial scales. -/
theorem aux_lem_15_u_init_numeric (C7 C8 B delta gam a : ℝ) (j j0 : ℕ) (hj : j ≤ j0)
    (hC7 : 0 ≤ C7) (hC8 : 0 ≤ C8) (hB : 0 ≤ B) (hdelta : 0 ≤ delta) (hgam : 0 ≤ gam)
    (ha : 0 ≤ a) :
    2 * (C7 * delta * ((3 : ℝ) ^ (-(j : ℝ))) ^ (-gam) *
        (C8 * ((3 : ℝ) ^ (-(j : ℝ))) ^ (-gam))) * B ≤
      (2 * (C7 * C8) * B * (3 : ℝ) ^ (2 * gam * j0) * (3 : ℝ) ^ (a * j0)) * delta *
        (3 : ℝ) ^ (-a * (j : ℝ)) := by
  have h3 : ((3 : ℝ) ^ (-(j : ℝ))) ^ (-gam) = (3 : ℝ) ^ (gam * j) := by
    rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
  rw [h3]
  have hjr : (j : ℝ) ≤ j0 := by exact_mod_cast hj
  have hE : (3 : ℝ) ^ (gam * j) * (3 : ℝ) ^ (gam * j) ≤
      (3 : ℝ) ^ (2 * gam * j0) * ((3 : ℝ) ^ (a * j0) * (3 : ℝ) ^ (-a * (j : ℝ))) := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
      ← Real.rpow_add (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have hc : 0 ≤ 2 * (C7 * C8) * B * delta := by positivity
  calc 2 * (C7 * delta * (3 : ℝ) ^ (gam * j) * (C8 * (3 : ℝ) ^ (gam * j))) * B
      = (2 * (C7 * C8) * B * delta) * ((3 : ℝ) ^ (gam * j) * (3 : ℝ) ^ (gam * j)) := by ring
    _ ≤ (2 * (C7 * C8) * B * delta) *
        ((3 : ℝ) ^ (2 * gam * j0) * ((3 : ℝ) ^ (a * j0) * (3 : ℝ) ^ (-a * (j : ℝ)))) :=
        mul_le_mul_of_nonneg_left hE hc
    _ = _ := by ring

theorem aux_lem_15_u_main
    (_hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (_hphi : ContDiff ℝ ∞ phi)
    (_hnonconst : ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), phi x ≠ phi y)
    (b : weakSobolevGraph (centeredCube z r hr))
    (_hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (f : SpatialCoordinates d → ℝ) (_hf : ContDiff ℝ ∞ f)
    (_hfc : HasCompactSupport f)
    (_hfsupp : tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (_hf0 : ∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), f x ≠ 0)
    (fL2 : DomainL2 (centeredCube z r hr))
    (_hfL2 : (fL2 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f)
    (t p B : ℝ) (ht_lower : (d : ℝ) - 1 < t) (_ht_upper : t < (d : ℝ))
    (hp : 2 ≤ p) (hB : 0 ≤ B) (dirichlet : Bool) :
    let S := killedResponseSpace hP
    let L := (sobolevVolumeLoad fL2).comp S.space.subtypeL
    ∃ C : ℝ, 0 < C ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
          (_G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
          (_G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw),
          let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
              C(SpatialCoordinates d, ℝ)) :=
            ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
          let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
            forget.continuous.measurable.aemeasurable
          let P := (commonScaleLaw d nu).toMeasure
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            Measurable H →
            (∀ᵐ omega ∂P,
              Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega))) →
          ∀ (kappa : ℕ → ℝ), (∀ N, 0 < kappa N) →
          ∀ (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr)),
            (∀ N omega,
              (aN N omega).val =ᵐ[volume.restrict
                (centeredCube z r hr : Set (SpatialCoordinates d))]
                (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N)))) →
          let RN : ℕ → BilateralField d → ℝ :=
            fun N omega =>
              if dirichlet then
                dirichletResponse S (aN N omega) b
              else
                inverseResponse S (aN N omega) L
          let gN : ℕ → BilateralField d → HilbertGradient (centeredCube z r hr) :=
            fun N omega =>
              if dirichlet then
                sobolevGradient (dirichletMinimizer S (aN N omega) b).val
              else
                subspaceGradient S.space (responseSolution S (aN N omega) L)
          ∀ (K : ℕ → BilateralField d → ℝ),
            ((∀ N, AEStronglyMeasurable (K N) P) ∧
            (∀ᵐ omega ∂P, ∀ N, 0 ≤ K N omega)) →
            (∀ᵐ omega ∂P, ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
              ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
                localGradientEnergy (aN N omega)
                  (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
                  (gN N omega) ≤ K N omega * rho ^ t) →
            (∀ N,
              MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
              MemLp (RN N) (ENNReal.ofReal (3 * p)) P ∧
              eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B ∧
              eLpNorm (RN N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
            ∀ (N j : ℕ), j ≤ N →
              eLpNorm
                (fun pair : BilateralField d × BilateralField d =>
                  RN N pair.1 -
                    RN N
                      (Function.update pair.1 (-(j : ℤ))
                        (pair.2 (-(j : ℤ)))))
                (ENNReal.ofReal p) (P.prod P) ≤
              ENNReal.ofReal
                (C * delta *
                  (3 : ℝ) ^
                  (-(t * (t - (d : ℝ) + 1) / (t + 1) /
                      (8 * Real.log 3)) * (j : ℝ)))
    := by
  intro S L
  have hd1 : 1 ≤ d := by omega
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d by omega))
  have hgeo := aux_lem_15_u_geom d hd1 (2 * Real.sqrt d) (by positivity)
  obtain ⟨Cd, hCd, hgeo⟩ := hgeo
  have hgeo2 := hgeo t ht_lower
  obtain ⟨hbpos, r0, hr0, _, hgeoR⟩ := hgeo2
  have hp0 : 0 < p := by linarith
  have hgam : 0 < t * (t - (d : ℝ) + 1) / (t + 1) / 12 := by positivity
  have hQne := aux_lem_15_u_Qt_nonempty z hr
  have hRt : 0 ≤ ‖z‖ + (r / 2 + 1) := by positivity
  have hQR := aux_lem_15_u_Qt_bound z r
  -- the uniform layer-moment bank
  have hLexp := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR p ((0 : ℕ) : ℝ) 2 _ hp0 (by norm_num) (by norm_num) hgam
  obtain ⟨Cexp, _, hLexp⟩ := hLexp
  have hLdel := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (2 * p) ((1 : ℕ) : ℝ) 4 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨Cdel, hCdel, hLdel⟩ := hLdel
  have hLa := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (2 * p) ((0 : ℕ) : ℝ) 7 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨Ca, hCa, hLa⟩ := hLa
  have hLb := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (2 * p) ((1 : ℕ) : ℝ) 7 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨Cb, hCb, hLb⟩ := hLb
  have hLc := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR 1 ((0 : ℕ) : ℝ) 8 _ (by norm_num) (by norm_num) (by norm_num) hgam
  obtain ⟨Cc, hCc, hLc⟩ := hLc
  have hLe := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR 1 ((2 : ℕ) : ℝ) 8 _ (by norm_num) (by norm_num) (by norm_num) hgam
  obtain ⟨Ce, hCe, hLe⟩ := hLe
  have hL7 := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (4 * p) ((1 : ℕ) : ℝ) 1 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨C7, hC7, hL7⟩ := hL7
  have hL8 := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (4 * p) ((0 : ℕ) : ℝ) 1 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨C8, hC8, hL8⟩ := hL8
  -- the Efron–Stein constant (BBLM, proved in `aux_lem_15_bblm`)
  have hIES := in_efron_stein aux_lem_15_bblm p hp
  obtain ⟨Cp, hCp, hCpall⟩ := hIES
  have hCpall' : ∀ (m : ℕ) (mu : Fin m → Measure C(SpatialCoordinates d, ℝ))
      [∀ i, IsProbabilityMeasure (mu i)], aux_lem_15_u_ESProp mu p Cp := by
    intro m mu _
    exact (hCpall m (fun _ => C(SpatialCoordinates d, ℝ)) mu).1
  -- the initial scales
  have hj0 := exists_pow_lt_of_lt_one hr0 (by norm_num : (1 / 3 : ℝ) < 1)
  obtain ⟨j0, hj0⟩ := hj0
  refine ⟨(4 * Cd * (max 1 r) ^ d * Cdel * B +
      4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
        (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) +
      2 * (C7 * C8) * B * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) * j0) + 1,
    by positivity, ?_⟩
  intro delta hdelta hdelta1 Praw hG1 hG2 forget nu P H hHmeas hHconv kappa _ aN haN RN gN K
    hKmn hgrowth hmom N j hjN
  obtain ⟨hKm, hKnn⟩ := hKmn
  have hmomN := hmom N
  obtain ⟨_, _, hmomK, hmomR⟩ := hmomN
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ha0 : 0 ≤ t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) := by positivity
  have hrs : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hY0 : 0 ≤ (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) * (j : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  by_cases hj : j0 ≤ j
  · -- masking case
    have hrsr0 : (3 : ℝ) ^ (-(j : ℝ)) ≤ r0 := by
      have h1 : (3 : ℝ) ^ (-(j : ℝ)) = (1 / 3 : ℝ) ^ j := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
      rw [h1]
      exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj).trans hj0.le
    have hgeom := hgeoR z r hr _ hrs hrsr0
    have hM1 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hLexp delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM2 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 1
      (hLdel delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM3 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hLa delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM4 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 1
      (hLb delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM5 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hLc delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM6 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 2
      (hLe delta hdelta hdelta1 Praw hG1 hG2 j)
    simp only [pow_zero, one_mul, pow_one, Real.rpow_natCast, ENNReal.ofReal_one,
      mul_one] at hM1 hM2 hM3 hM4 hM5 hM6
    have hmask := aux_lem_15_u_mask_case d hd z r hr S dirichlet b L t p B hp hB Cd hCd hbpos
      Cp hCp hCpall' _ Cdel Ca Cb Cc Ce hCdel.le hCa.le hCb.le hCc.le hCe.le delta hdelta
      hdelta1 Praw hG1 hG2 H hHmeas hHconv kappa aN haN K hKm hKnn hgrowth N j hjN hmomK
      hmomR _ rfl hgeom hM1 hM2 hM3 hM4 hM5 hM6
    refine hmask.trans (ENNReal.ofReal_le_ofReal ?_)
    have hexp := aux_lem_15_u_exponent (t * (t - (d : ℝ) + 1) / (t + 1)) hbpos.le j
    have hrw : ((3 : ℝ) ^ (-(j : ℝ))) ^ (3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) =
        (3 : ℝ) ^ (-(3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) * (j : ℝ)) := by
      rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
    rw [hrw]
    have hK0 : 0 ≤ 4 * Cd * (max 1 r) ^ d * Cdel * B +
        4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
          (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B := by positivity
    have hKi : 0 ≤ 2 * (C7 * C8) * B * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) * j0) := by positivity
    calc (4 * Cd * (max 1 r) ^ d * Cdel * B +
          4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
            (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) * delta *
          (3 : ℝ) ^ (-(3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) * (j : ℝ))
        ≤ (4 * Cd * (max 1 r) ^ d * Cdel * B +
          4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
            (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) * delta *
          (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) * (j : ℝ)) := by
          gcongr
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hdelta.le) hY0
          linarith
  · -- initial scales
    push_neg at hj
    have hM7 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 1
      (hL7 delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM8 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hL8 delta hdelta hdelta1 Praw hG1 hG2 j)
    simp only [pow_zero, one_mul, pow_one, Real.rpow_natCast, mul_one] at hM7 hM8
    have hinit := aux_lem_15_u_init_case d hd z r hr S dirichlet b L t p B hp delta hdelta
      hdelta1 Praw hG1 hG2 H hHmeas hHconv kappa aN haN K hKnn hgrowth N j hjN hmomR _ _
      (by positivity) (by positivity) hM7 hM8
    refine hinit.trans (ENNReal.ofReal_le_ofReal ?_)
    have hnum := aux_lem_15_u_init_numeric C7 C8 B delta
      (t * (t - (d : ℝ) + 1) / (t + 1) / 12)
      (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) j j0 hj.le hC7.le hC8.le hB
      hdelta.le hgam.le ha0
    have hK0 : 0 ≤ 4 * Cd * (max 1 r) ^ d * Cdel * B +
        4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
          (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B := by positivity
    have hd0 : 0 ≤ delta := hdelta.le
    refine hnum.trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hd0) hY0
    linarith


end UniformFourTerm

open scoped ContDiff




theorem lem_15
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (hnonconst : ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), phi x ≠ phi y)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (f : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f)
    (hfsupp : tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hf0 : ∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), f x ≠ 0)
    (fL2 : DomainL2 (centeredCube z r hr))
    (hfL2 : (fL2 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f)
    (t p B : ℝ) (ht_lower : (d : ℝ) - 1 < t) (ht_upper : t < (d : ℝ))
    (hp : 2 ≤ p) (hB : 0 ≤ B) (dirichlet : Bool) :
    let S := killedResponseSpace hP
    let L := (sobolevVolumeLoad fL2).comp S.space.subtypeL
    ∃ C : ℝ, 0 < C ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
          (_G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
          (_G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw),
          let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
              C(SpatialCoordinates d, ℝ)) :=
            ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
          let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
            forget.continuous.measurable.aemeasurable
          let P := (commonScaleLaw d nu).toMeasure
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            Measurable H →
            (∀ᵐ omega ∂P,
              Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega))) →
          ∀ (kappa : ℕ → ℝ), (∀ N, 0 < kappa N) →
          ∀ (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr)),
            (∀ N omega,
              (aN N omega).val =ᵐ[volume.restrict
                (centeredCube z r hr : Set (SpatialCoordinates d))]
                (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N)))) →
          let RN : ℕ → BilateralField d → ℝ :=
            fun N omega =>
              if dirichlet then
                dirichletResponse S (aN N omega) b
              else
                inverseResponse S (aN N omega) L
          let gN : ℕ → BilateralField d → HilbertGradient (centeredCube z r hr) :=
            fun N omega =>
              if dirichlet then
                sobolevGradient (dirichletMinimizer S (aN N omega) b).val
              else
                subspaceGradient S.space (responseSolution S (aN N omega) L)
          ∀ (K : ℕ → BilateralField d → ℝ),
            ((∀ N, AEStronglyMeasurable (K N) P) ∧
            (∀ᵐ omega ∂P, ∀ N, 0 ≤ K N omega)) →
            (∀ᵐ omega ∂P, ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
              ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
                localGradientEnergy (aN N omega)
                  (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
                  (gN N omega) ≤ K N omega * rho ^ t) →
            (∀ N,
              MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
              MemLp (RN N) (ENNReal.ofReal (3 * p)) P ∧
              eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B ∧
              eLpNorm (RN N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
            ∀ (N j : ℕ), j ≤ N →
              eLpNorm
                (fun pair : BilateralField d × BilateralField d =>
                  RN N pair.1 -
                    RN N
                      (Function.update pair.1 (-(j : ℤ))
                        (pair.2 (-(j : ℤ)))))
                (ENNReal.ofReal p) (P.prod P) ≤
              ENNReal.ofReal
                (C * delta *
                  (3 : ℝ) ^
                  (-(t * (t - (d : ℝ) + 1) / (t + 1) /
                      (8 * Real.log 3)) * (j : ℝ)))
    := by
  exact aux_lem_15_u_main hES d hd z r hr hP phi hphi hnonconst b hb
    f hf hfc hfsupp hf0 fL2 hfL2 t p B ht_lower ht_upper hp hB dirichlet

end Paper
