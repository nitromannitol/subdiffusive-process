module

public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import Mathlib.MeasureTheory.Measure.Tight
public import MarkovProcess.Continuity.PathModulus
public import MarkovProcess.Continuity.PathTightness

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_in_cutoff_local_path_tightness_tsum_geometric_half (eps : ℝ≥0∞) :
    (∑' n : ℕ, eps * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹) = eps := by
  have hsplit : ∀ n : ℕ, ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ =
      2⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ n := by
    intro n
    rw [pow_succ, ENNReal.mul_inv (by simp) (by simp), ← ENNReal.inv_pow]
    ring
  have hone : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
    rw [← ENNReal.inv_two_add_inv_two, ENNReal.add_sub_cancel_left (by simp)]
  rw [ENNReal.tsum_mul_left]
  simp_rw [hsplit]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, hone, inv_inv,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]



theorem in_cutoff_local_path_tightness
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (_hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (_hin : in_crossing M H PN KN)
    (hlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ T : ℝ≥0, ∀ r : ℝ≥0∞, 0 < r → ∀ eta : ℝ≥0∞, 0 < eta →
          (∃ delta : ℝ≥0∞, 0 < delta ∧
            ∀ x ∈ B,
              ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
                ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
                (ContinuousPath.modulusSet T delta r)ᶜ ≤ eta) ∧
          (∃ K0 : Set (SpatialCoordinates d), IsCompact K0 ∧
            ∀ x ∈ B,
              ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
                ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
                {path : DiffusionPath d | ∀ s : ℝ≥0, s ≤ T → path s ∈ K0}ᶜ ≤ eta)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ eps : ℝ, 0 < eps →
          ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧
            ∀ x ∈ B,
              ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
                ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
                  Ksetᶜ ≤ ENNReal.ofReal eps := by
  filter_upwards [hlocal] with omega homega
  intro N B hB eps heps
  let e : ℝ≥0∞ := ENNReal.ofReal eps
  have he : 0 < e := by
    exact ENNReal.ofReal_pos.mpr heps
  let a : ℝ≥0∞ := e * (2 : ℝ≥0∞)⁻¹
  have ha : 0 < a := by
    exact ENNReal.mul_pos he.ne' (by simp)
  let rho : ℕ → ℝ≥0∞ := fun n ↦ (n : ℝ≥0∞)⁻¹
  have hrhopos : ∀ n : ℕ, 0 < rho n := by
    intro n
    exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top n)
  have hrhotendsto : Tendsto rho atTop (nhds 0) := by
    exact ENNReal.tendsto_inv_nat_nhds_zero
  have hmodulus : ∀ n : ℕ, ∃ delta : ℝ≥0∞, 0 < delta ∧
      ∀ x ∈ B,
        ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
          ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
          (ContinuousPath.modulusSet (n : ℝ≥0) (delta) (rho n))ᶜ ≤
            a * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ := by
    intro n
    have hpos : 0 < a * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ := by
      exact ENNReal.mul_pos ha.ne' (by simp)
    exact (homega N B hB (n : ℝ≥0) (rho n) (hrhopos n)
      (a * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹) hpos).1
  choose delta hdelta hdelta_measure using hmodulus
  obtain ⟨K0, hK0, hK0_measure⟩ :=
    (homega N B hB (0 : ℝ≥0) (1 : ℝ≥0∞) one_pos a ha).2
  let Kset : Set (DiffusionPath d) :=
    ContinuousPath.moduliSet K0 delta rho
  refine ⟨Kset, ContinuousPath.isCompact_moduliSet hK0 hdelta hrhotendsto, ?_⟩
  intro x hx
  have hstart_subset :
      {path : DiffusionPath d | path 0 ∉ K0} ⊆
        {path : DiffusionPath d | ∀ s : ℝ≥0, s ≤ 0 → path s ∈ K0}ᶜ := by
    intro path hpath hpath0
    exact hpath (hpath0 0 le_rfl)
  have hstart :
      ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
        ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
        {path : DiffusionPath d | path 0 ∉ K0} ≤ a := by
    exact (measure_mono hstart_subset).trans (hK0_measure x hx)
  have hcompl : Ksetᶜ =
      {path : DiffusionPath d | path 0 ∉ K0} ∪
        ⋃ n : ℕ, (ContinuousPath.modulusSet (n : ℝ≥0) (delta n) (rho n))ᶜ := by
    ext path
    simp only [Kset, ContinuousPath.moduliSet, Set.mem_compl_iff, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, not_and_or,
      not_forall]
  rw [hcompl]
  calc
    ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
        ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
        ({path : DiffusionPath d | path 0 ∉ K0} ∪
          ⋃ n : ℕ, (ContinuousPath.modulusSet (n : ℝ≥0) (delta n) (rho n))ᶜ)
        ≤ ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
            ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
            {path : DiffusionPath d | path 0 ∉ K0} +
          ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
            ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
            (⋃ n : ℕ, (ContinuousPath.modulusSet (n : ℝ≥0) (delta n) (rho n))ᶜ) :=
      measure_union_le _ _
    _ ≤ a + ∑' n : ℕ,
          ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
            ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
            (ContinuousPath.modulusSet (n : ℝ≥0) (delta n) (rho n))ᶜ := by
      exact add_le_add hstart (measure_iUnion_le _)
    _ ≤ a + ∑' n : ℕ, a * ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ := by
      exact add_le_add le_rfl (ENNReal.tsum_le_tsum fun n ↦ hdelta_measure n x hx)
    _ = e := by
      rw [aux_in_cutoff_local_path_tightness_tsum_geometric_half]
      dsimp [a]
      rw [← mul_add]
      simp [ENNReal.inv_two_add_inv_two]

end SubdiffusiveProcess.Paper
