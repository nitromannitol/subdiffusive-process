import SubdiffusiveProcess.Section10.InitialSimplexEnergyAnnealed

/-!
# Exact geometric interface for a finite simplex cube packing

The only unconstructed supplier for the full initial bound is geometry: a
finite multiscale packing and its volume fractions. This structure contains
no coefficient, probability law, minimizer, or promised energy estimate.
Truncation at depth ell leaves a remainder on which the affine function is
used. The analytic supplier computes that remainder's energy exactly.
-/

namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- Cubes inside the scale-ell simplex, with summable per-depth volume and a
small remainder. `K` is chosen independently of ell and the permutation. -/
structure InitialSimplexCubePacking (ell : ℕ) (pi : Equiv.Perm (Fin d)) (K : ℝ) where
  cubes : Finset (TriadicCube d)
  depth : TriadicCube d → ℕ
  depth_pos : ∀ Q ∈ cubes, 0 < depth Q
  depth_le : ∀ Q ∈ cubes, depth Q ≤ ell
  scale_eq : ∀ Q ∈ cubes, Q.scale = ((ell - depth Q : ℕ) : ℤ)
  subset : ∀ Q ∈ cubes, openCubeSet Q ⊆ (initialSimplex ell pi).openCarrier
  disjoint : (cubes : Set (TriadicCube d)).PairwiseDisjoint openCubeSet
  depth_fraction : ∀ i : ℕ,
    (∑ Q ∈ cubes.filter (fun Q => depth Q = i),
      (volume (openCubeSet Q)).toReal /
        (volume (initialSimplex ell pi).openCarrier).toReal) ≤ K * (1 / 3 : ℝ) ^ i
  remainder_fraction :
    (volume (packingRemainder (initialSimplex ell pi).openCarrier cubes openCubeSet)).toReal /
      (volume (initialSimplex ell pi).openCarrier).toReal ≤ K * (1 / 3 : ℝ) ^ ell

/-- At ell=0 no packed cube is allowed. -/
theorem InitialSimplexCubePacking.cubes_zero (pi : Equiv.Perm (Fin d)) {K : ℝ}
    (P : InitialSimplexCubePacking 0 pi K) : P.cubes = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro Q hQ
  have hpos := P.depth_pos Q hQ
  have hle := P.depth_le Q hQ
  omega

/-- The actual zero-scale geometry is the empty packing and full affine
remainder. This constructs the complete geometric supplier at ell=0. -/
def initialSimplexCubePacking_zero (pi : Equiv.Perm (Fin d)) {K : ℝ} (hK : 1 ≤ K) :
    InitialSimplexCubePacking 0 pi K where
  cubes := ∅
  depth := fun _ => 0
  depth_pos := by simp only [Finset.notMem_empty, false_implies, implies_true]
  depth_le := by simp only [Finset.notMem_empty, false_implies, implies_true]
  scale_eq := by simp only [Finset.notMem_empty, false_implies, implies_true]
  subset := by simp only [Finset.notMem_empty, false_implies, implies_true]
  disjoint := by simp only [Finset.coe_empty, pairwiseDisjoint_empty]
  depth_fraction := by
    intro i
    simp only [Finset.filter_empty, Finset.sum_empty]
    exact mul_nonneg (le_trans (by norm_num) hK) (pow_nonneg (by norm_num) i)
  remainder_fraction := by
    have hvol : (volume (initialSimplex 0 pi).openCarrier).toReal ≠ 0 :=
      (volume_toReal_pos (kuhnCellDomain (initialSimplex 0 pi))).ne'
    simpa only [packingRemainder, Finset.notMem_empty, iUnion_of_empty,
      iUnion_empty, diff_empty, div_self hvol, pow_zero, mul_one] using hK

end
end SubdiffusiveProcess.Section10
