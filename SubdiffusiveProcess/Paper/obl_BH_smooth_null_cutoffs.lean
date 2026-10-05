module

public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import SubdiffusiveProcess.DirichletForm.All

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff Manifold

namespace SubdiffusiveProcess.Paper

lemma aux_obl_BH_smooth_null_cutoffs_smooth
    (K U : Set ℝ) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ phi : ℝ → ℝ,
      ContDiff ℝ ∞ phi ∧
        (∀ x : ℝ, 0 ≤ phi x ∧ phi x ≤ 1) ∧
        (∀ x ∈ K, phi x = 1) ∧
        tsupport phi ⊆ U := by
  obtain ⟨L, hLcompact, hLclosed, hKL, hLU⟩ :=
    exists_compact_closed_between hK hU hKU
  obtain ⟨f, hf_one, hf_zero, hf_range⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓘(ℝ, ℝ)) hK.isClosed hKL
  have hf_smooth : ContDiff ℝ ∞ (f : ℝ → ℝ) := f.contMDiff.contDiff
  have hf_support : Function.support (f : ℝ → ℝ) ⊆ L := by
    intro x hx
    by_contra hxL
    exact hx (hf_zero x hxL)
  have hf_tsupport : tsupport (f : ℝ → ℝ) ⊆ L := by
    change closure (Function.support (f : ℝ → ℝ)) ⊆ L
    exact closure_minimal hf_support hLclosed
  refine ⟨f, hf_smooth, ?_, ?_, hf_tsupport.trans hLU⟩
  · intro x
    exact ⟨(hf_range x).1, (hf_range x).2⟩
  · intro x hx
    exact hf_one.self_of_nhdsSet x hx

/--
Fine proof-step child of obl_BH.

Carried-input Scope and inputs:
- K is the compact Lebesgue-null subset of the value line used by the
  manuscript; no form carrier is introduced.
- Each U n is open, contains K, and has the quantitative length bound
  used later in the L2 estimate.
- Each phi n is smooth, takes values in [0,1], equals one on K, and
  has closed support inside U n.
- This is a construction conclusion, not a carried cutoff hypothesis.
-/
theorem obl_BH_smooth_null_cutoffs
    (K : Set ℝ) (hK : IsCompact K) (hKnull : volume K = 0) :
    ∃ (U : ℕ → Set ℝ) (phi : ℕ → ℝ → ℝ),
      (∀ n : ℕ,
        IsOpen (U n) ∧ K ⊆ U n ∧
          volume.real (U n) ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ,
        ContDiff ℝ ∞ (phi n) ∧
          (∀ x : ℝ, 0 ≤ phi n x ∧ phi n x ≤ 1) ∧
          (∀ x ∈ K, phi n x = 1) ∧
          tsupport (phi n) ⊆ U n) := by
  have hU : ∀ n : ℕ, ∃ U : Set ℝ,
      K ⊆ U ∧ IsOpen U ∧ volume U < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    have hn : 0 < (1 / ((n : ℝ) + 1) : ℝ) := by positivity
    apply Set.exists_isOpen_lt_of_lt K (ENNReal.ofReal (1 / ((n : ℝ) + 1)))
    rw [hKnull]
    exact ENNReal.ofReal_pos.mpr hn
  choose U hKU hUopen hUmeasure using hU
  have hUreal : ∀ n : ℕ, volume.real (U n) ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have hn : 0 ≤ (1 / ((n : ℝ) + 1) : ℝ) := by positivity
    have hlt : (volume (U n)).toReal < (ENNReal.ofReal (1 / ((n : ℝ) + 1))).toReal :=
      (ENNReal.toReal_lt_toReal (ne_of_lt ((hUmeasure n).trans_le le_top))
        ENNReal.ofReal_ne_top).mpr (hUmeasure n)
    rw [ENNReal.toReal_ofReal hn] at hlt
    exact hlt.le
  have hphi : ∀ n : ℕ, ∃ phi : ℝ → ℝ,
      ContDiff ℝ ∞ phi ∧
        (∀ x : ℝ, 0 ≤ phi x ∧ phi x ≤ 1) ∧
        (∀ x ∈ K, phi x = 1) ∧
        tsupport phi ⊆ U n := by
    intro n
    exact aux_obl_BH_smooth_null_cutoffs_smooth K (U n) hK (hUopen n) (hKU n)
  choose phi hphi_smooth hphi_range hphi_one hphi_support using hphi
  refine ⟨U, phi, ?_, ?_⟩
  · intro n
    exact ⟨hUopen n, hKU n, hUreal n⟩
  · intro n
    exact ⟨hphi_smooth n, hphi_range n, hphi_one n, hphi_support n⟩

end SubdiffusiveProcess.Paper
