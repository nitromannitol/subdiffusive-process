module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerInteriorHolder
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.DomainMonotonicity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.TranslatedFinitePResidualLift
public import Homogenization.Geometry.ConvexDomain
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

/-!
# Interior Hölder representatives for bounded massive weak solutions

A translated origin cube contained in the open carrier supplies a finite-exponent
divergence lift at each point. The resulting local Schauder representatives agree
with the canonical ball-average representative. Countable and finite covers give
global continuity and one Hölder constant on each compact subset.
-/

set_option autoImplicit false

open MeasureTheory Topology Homogenization Set
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower

variable {d : ℕ}

/-- Every point of an open set lies in a translated origin cube contained in
that set. The translation is the point itself. -/
theorem exists_translated_originCube_subset_of_isOpen
    {W : Set (Vec d)} (hW : IsOpen W) {x : Vec d} (hx : x ∈ W) :
    ∃ m : ℤ, x ∈ translateSet x (openCubeSet (originCube d m)) ∧
      translateSet x (openCubeSet (originCube d m)) ⊆ W := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hW x hx
  obtain ⟨m, hm, -⟩ := exists_mem_Ico_zpow hr (by norm_num : (1 : ℝ) < 3)
  have hmpos : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  refine ⟨m, ?_, ?_⟩
  · rw [mem_translateSet_iff_sub_mem, sub_self, mem_openCubeSet_originCube_iff]
    intro i
    simp only [Pi.zero_apply]
    constructor <;> linarith
  · intro y hy
    apply hball
    apply (dist_pi_lt_iff hr).2
    intro i
    have hyi := (mem_openCubeSet_originCube_iff.1
      (mem_translateSet_iff_sub_mem.1 hy)) i
    rw [Real.dist_eq, abs_lt]
    change -(1 / 2 : ℝ) * (3 : ℝ) ^ m < y i - x i ∧
      y i - x i < (1 / 2 : ℝ) * (3 : ℝ) ^ m at hyi
    constructor <;> linarith [hyi.1, hyi.2]

/-- Local continuous representatives of the canonical ball averages assemble on
an arbitrary open carrier. -/
theorem continuousOn_and_ae_eq_euclideanBallAverageRepresentative_of_local
    {W : Set (Vec d)} (hW : IsOpen W) {u : Vec d → ℝ}
    (hlocal : ∀ x ∈ W, ∃ r : ℝ, 0 < r ∧ euclideanBall x r ⊆ W ∧
      ContinuousOn (euclideanBallAverageRepresentative u) (euclideanBall x r) ∧
        euclideanBallAverageRepresentative u =ᵐ[volume.restrict (euclideanBall x r)] u) :
    ContinuousOn (euclideanBallAverageRepresentative u) W ∧
      euclideanBallAverageRepresentative u =ᵐ[volume.restrict W] u := by
  have hlocal' : ∀ q : W, ∃ r : ℝ, 0 < r ∧ euclideanBall (q : Vec d) r ⊆ W ∧
      ContinuousOn (euclideanBallAverageRepresentative u)
        (euclideanBall (q : Vec d) r) ∧
      euclideanBallAverageRepresentative u
        =ᵐ[volume.restrict (euclideanBall (q : Vec d) r)] u :=
    fun q => hlocal q q.2
  choose r hr hsub hcont hae using hlocal'
  let V : W → Set (Vec d) := fun q => euclideanBall (q : Vec d) (r q)
  have hVopen : ∀ q, IsOpen (V q) := fun q => isOpen_euclideanBall (q : Vec d) (r q)
  have hVsub : ∀ q, V q ⊆ W := fun q => hsub q
  have hVself : ∀ q, (q : Vec d) ∈ V q := by
    intro q
    change euclideanSqDist (q : Vec d) (q : Vec d) < (r q) ^ 2
    rw [euclideanSqDist_self]
    exact sq_pos_of_pos (hr q)
  have hVunion : (⋃ q, V q) = W := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨q, hxq⟩ := Set.mem_iUnion.1 hx
      exact hVsub q hxq
    · intro x hx
      exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hVself ⟨x, hx⟩⟩
  obtain ⟨T, hTcount, hTunion⟩ :=
    TopologicalSpace.isOpen_iUnion_countable V hVopen
  let I := T
  letI : Countable I := hTcount.to_subtype
  let VT : I → Set (Vec d) := fun q => V q.1
  have hcover : W ⊆ ⋃ q : I, VT q := by
    intro x hx
    have hxall : x ∈ ⋃ q, V q := by rw [hVunion]; exact hx
    rw [← hTunion] at hxall
    simp only [Set.mem_iUnion] at hxall ⊢
    obtain ⟨q, hqT, hxq⟩ := hxall
    exact ⟨⟨q, hqT⟩, hxq⟩
  constructor
  · intro x hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.1 (hcover hx)
    exact ((hcont q.1).continuousAt ((hVopen q.1).mem_nhds hxq)).continuousWithinAt
  · have hn : ∀ q : I, ∀ᵐ x ∂volume,
        x ∈ VT q → euclideanBallAverageRepresentative u x = u x :=
      fun q => (ae_restrict_iff' (hVopen q.1).measurableSet).1 (hae q.1)
    apply (ae_restrict_iff' hW.measurableSet).2
    filter_upwards [ae_all_iff.2 hn] with x hx hxW
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.1 (hcover hxW)
    exact hx q hxq

/-- A bounded massive solution with bounded forcing has a canonical Hölder
representative near each point of any open carrier. -/
theorem exists_frozenBall_holder_of_bounded_massiveWeakSolution
    [NeZero d] (hd : 2 ≤ d) {W : Set (Vec d)} (hW : IsOpen W)
    {c rho : Vec d → ℝ} (hc : ContinuousOn c W) (hcpos : ∀ x ∈ W, 0 < c x)
    {mu rhoMax M F : ℝ} {u : H1Function W} {f : Vec d → ℝ}
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    (hf : MemL2On W f)
    (hfBound : ∀ᵐ x ∂(volume.restrict W), |f x| ≤ F)
    (huBound : ∀ᵐ x ∂(volume.restrict W), |u.toFun x| ≤ M)
    (hu : IsMassiveWeakSolutionOn c rho mu W u f) {x : Vec d} (hx : x ∈ W) :
    ∃ r : ℝ, 0 < r ∧ euclideanBall x r ⊆ W ∧ ∃ C : ℝ, 0 ≤ C ∧
      EuclideanHolderBoundOn (euclideanBall x r) (1 / 2) C
        (euclideanBallAverageRepresentative u.toFun) ∧
      ContinuousOn (euclideanBallAverageRepresentative u.toFun) (euclideanBall x r) ∧
      euclideanBallAverageRepresentative u.toFun
        =ᵐ[volume.restrict (euclideanBall x r)] u.toFun := by
  obtain ⟨m, hxm, hmW⟩ := exists_translated_originCube_subset_of_isOpen hW hx
  have hQ := (isOpenBoundedConvexDomain_openCubeSet (originCube d m)).translateSet x
  obtain ⟨g, _, hgWeak, hgLp⟩ :=
    exists_schauder_divergence_lift_of_bounded_massiveWeakSolution_translateSet d hd x
      (hrhoMeas.mono_measure (Measure.restrict_mono hmW le_rfl))
      (ae_restrict_of_ae_restrict_of_subset hmW hrhoBdd)
      (memL2On_mono hmW hf)
      (ae_restrict_of_ae_restrict_of_subset hmW hfBound)
      (ae_restrict_of_ae_restrict_of_subset hmW huBound)
      (IsMassiveWeakSolutionOn.restrict hQ.isOpen hW hmW hu)
  have hp : schauderSourceExponent d (1 / 2) = 2 * (d : ℝ) := by
    unfold schauderSourceExponent
    norm_num
    ring
  rw [← hp] at hgLp
  obtain ⟨r, hr, hrQ, C, hC, hhold, hcont, hae⟩ :=
    exists_frozenBall_euclideanHolderBoundOn hd hQ.isOpen (hc.mono hmW)
      (fun y hy => hcpos y (hmW hy)) hgWeak hgLp hxm
  exact ⟨r, hr, hrQ.trans hmW, C, hC, hhold, hcont, hae⟩

/-- A bounded massive solution with bounded forcing has a continuous
representative on its whole open carrier, Hölder-`1/2` on every compact subset.
The constant can depend on the solution; uniform boundedness removes that
dependence when this theorem is applied to a linear family. -/
theorem holder_euclideanBallAverageRepresentative_of_bounded_massiveWeakSolution
    [NeZero d] (hd : 2 ≤ d) {W : Set (Vec d)} (hW : IsOpen W)
    {c rho : Vec d → ℝ} (hc : ContinuousOn c W) (hcpos : ∀ x ∈ W, 0 < c x)
    {mu rhoMax M F : ℝ} {u : H1Function W} {f : Vec d → ℝ}
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    (hf : MemL2On W f)
    (hfBound : ∀ᵐ x ∂(volume.restrict W), |f x| ≤ F)
    (huBound : ∀ᵐ x ∂(volume.restrict W), |u.toFun x| ≤ M)
    (hu : IsMassiveWeakSolutionOn c rho mu W u f) :
    ContinuousOn (euclideanBallAverageRepresentative u.toFun) W ∧
      euclideanBallAverageRepresentative u.toFun =ᵐ[volume.restrict W] u.toFun ∧
      ∀ K : Set (Vec d), K ⊆ W → IsCompact K → ∃ C : ℝ,
        ∀ x ∈ K, ∀ y ∈ K,
          |euclideanBallAverageRepresentative u.toFun x -
            euclideanBallAverageRepresentative u.toFun y| ≤
              C * dist x y ^ ((1 : ℝ) / 2) := by
  have hlocal := fun x hx =>
    exists_frozenBall_holder_of_bounded_massiveWeakSolution hd hW hc hcpos
      hrhoMeas hrhoBdd hf hfBound huBound hu (x := x) hx
  obtain ⟨hcont, hae⟩ :=
    continuousOn_and_ae_eq_euclideanBallAverageRepresentative_of_local hW
      (fun x hx => by
        obtain ⟨r, hr, hrW, _, _, _, hrc, hrae⟩ := hlocal x hx
        exact ⟨r, hr, hrW, hrc, hrae⟩)
  refine ⟨hcont, hae, fun K hKW hK => ?_⟩
  obtain ⟨C, hC, hCK⟩ := exists_euclideanHolderBoundOn_compact_of_local huBound hK
    (fun x hx => hlocal x (hKW hx))
  refine ⟨C * (d : ℝ) ^ ((1 : ℝ) / 2), fun x hx y hy => ?_⟩
  calc
    _ ≤ C * euclideanDist x y ^ ((1 : ℝ) / 2) := hCK x hx y hy
    _ ≤ C * ((d : ℝ) * dist x y) ^ ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (euclideanNorm_nonneg _)
          (euclideanDist_le_dimension_mul_dist x y) (by norm_num)) hC
    _ = _ := by rw [Real.mul_rpow (by positivity) dist_nonneg, mul_assoc]

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
