import SubdiffusiveProcess.Section10.RetainedPrefixSparseStepSupport
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerCube

/-!
# Finite simplex-to-cube readout of the retained-prefix energy

The cube is its own finite Kuhn self-partition. Generic MeshGluing with
outer field one and competitor zero glues the actual retained minima.
The expectation bound consumes precisely the lawful retained induction bound.
-/

namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory ProbabilityTheory Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn

noncomputable section

variable {d : ℕ}

/-- The actual normalized retained-prefix continuum minimum on a cube. -/
def retainedPrefixCubeEnergy (M : GMCModel d) (ell R N : ℕ) (Q : TriadicCube d)
    (omega : PotentialSample d) (p : Vec d) : ℝ :=
  (volume (openCubeSet Q)).toReal⁻¹ *
    dirichletInfOn (retainedPrefixCoefficient M ell R N omega) (openCubeSet Q) p

/-- Finite self-partition gluing with outer field one and zero mesh competitor. -/
theorem retainedPrefixCubeEnergy_le_sum (M : GMCModel d) (ell R N : ℕ)
    (Q : TriadicCube d) (p : Vec d) (omega : PotentialSample d) :
    retainedPrefixCubeEnergy M ell R N Q omega p ≤
      ∑ T ∈ triadicSimplexPartition Q Q.scale,
        (volume T.openCarrier).toReal / (volume (openCubeSet Q)).toReal *
          retainedPrefixEnergy M ell R N T omega p := by
  classical
  set S : Finset (KuhnCell d) := triadicSimplexPartition Q Q.scale with hS
  set A : Vec d → ℝ := retainedPrefixCoefficient M ell R N omega with hA'
  have hA : Continuous A := continuous_retainedPrefixCoefficient M ell R N omega
  have hA0 : ∀ x, 0 ≤ A x := fun x => (retainedPrefixCoefficient_pos M ell R N omega x).le
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
      (scalarCoeffOnDataOfContinuousPos hA
        (retainedPrefixCoefficient_pos M ell R N omega) (kuhnCellDomain T)) hA0 _
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
  rw [retainedPrefixCubeEnergy]
  have hmul := mul_le_mul_of_nonneg_left hmain
    (show (0 : ℝ) ≤ (volume (openCubeSet Q)).toReal⁻¹ by positivity)
  refine hmul.trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [retainedPrefixEnergy]
  have hTpos : (volume T.openCarrier).toReal ≠ 0 :=
    ne_of_gt (volume_toReal_pos (kuhnCellDomain T))
  field_simp
  rw [hA']

/-- Nonnegativity of the actual energy forces any lawful induction constant
to be nonnegative; callers of the readout need not supply this separately. -/
theorem retainedPrefixSparseBound_nonneg (M : GMCModel d) (ell R N : ℕ)
    {kap : ℝ} (hIH : RetainedPrefixSparseBound M ell R N kap) : 0 ≤ kap := by
  let i : Fin d := ⟨0, by have := M.shellPrefix.dimension; omega⟩
  let T := dilatedCell (ell + N * R) (fun _ => 0) (Equiv.refl (Fin d))
  have hnn : 0 ≤ ∫ omega, retainedPrefixEnergy M ell R N T omega (Pi.single i (1 : ℝ))
      ∂M.P.toMeasure := by
    refine integral_nonneg fun omega => ?_
    exact mul_nonneg (by positivity)
      (dirichletInfOn_nonneg (isOpen_openCarrier T).measurableSet
        (fun x => (retainedPrefixCoefficient_pos M ell R N omega x).le))
  have h := hIH (fun _ => 0) (Equiv.refl (Fin d)) (Pi.single i (1 : ℝ))
  rw [vecNormSq_single, mul_one] at h
  exact hnn.trans h

/-- The simplex induction bound controls the retained field on every cube
at the retained scale, by finite self-partition gluing. -/
theorem integral_retainedPrefixCubeEnergy_le (M : GMCModel d) (ell R N : ℕ)
    {kap : ℝ} (hIH : RetainedPrefixSparseBound M ell R N kap)
    (Q : TriadicCube d) (hQ : Q.scale = ((ell + N * R : ℕ) : ℤ)) (p : Vec d) :
    ∫ omega, retainedPrefixCubeEnergy M ell R N Q omega p ∂M.P.toMeasure ≤
      kap * vecNormSq p := by
  classical
  let S := triadicSimplexPartition Q Q.scale
  have hUpos : 0 < (volume (openCubeSet Q)).toReal :=
    volume_toReal_pos (Ch02.cubeDomain Q)
  have hterm : ∀ T ∈ S, Integrable (fun omega : PotentialSample d =>
      (volume T.openCarrier).toReal / (volume (openCubeSet Q)).toReal *
        retainedPrefixEnergy M ell R N T omega p) M.P.toMeasure := fun T _ =>
    (integrable_retainedPrefixEnergy M ell R N T p).const_mul _
  have hle := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun omega =>
      mul_nonneg (by positivity)
        (dirichletInfOn_nonneg (isOpen_openCubeSet Q).measurableSet
          (fun x => (retainedPrefixCoefficient_pos M ell R N omega x).le)))
    (integrable_finset_sum S hterm)
    (Filter.Eventually.of_forall fun omega =>
      retainedPrefixCubeEnergy_le_sum M ell R N Q p omega)
  refine hle.trans ?_
  rw [integral_finset_sum S hterm]
  have hcell : ∀ T ∈ S,
      ∫ omega, (volume T.openCarrier).toReal / (volume (openCubeSet Q)).toReal *
        retainedPrefixEnergy M ell R N T omega p ∂M.P.toMeasure ≤
      (volume T.openCarrier).toReal / (volume (openCubeSet Q)).toReal *
        (kap * vecNormSq p) := by
    intro T hT
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hTscale : T.supportCube.scale = ((ell + N * R : ℕ) : ℤ) := by
      rw [supportCube_eq_of_mem_selfPartition hT, hQ]
    rw [eq_dilatedCell hTscale]
    exact hIH _ _ p
  refine (Finset.sum_le_sum hcell).trans ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ T ∈ S,
      (volume T.openCarrier).toReal / (volume (openCubeSet Q)).toReal ≤ 1 := by
    rw [← Finset.sum_div, div_le_one hUpos]
    exact sum_volume_openCarrier_selfPartition_le Q
  have hkap : 0 ≤ kap := retainedPrefixSparseBound_nonneg M ell R N hIH
  calc
    (∑ T ∈ S, (volume T.openCarrier).toReal / (volume (openCubeSet Q)).toReal) *
        (kap * vecNormSq p) ≤ 1 * (kap * vecNormSq p) :=
      mul_le_mul_of_nonneg_right hsum (mul_nonneg hkap (vecNormSq_nonneg p))
    _ = kap * vecNormSq p := one_mul _

end

end SubdiffusiveProcess.Section10
