module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCellContraction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecayFunction

@[expose] public section

/-!
# The exterior row, reduced to the geometry of the stopping partition

The proof establishes the exterior estimate
 in four steps:

1. the local `L²` contraction on the centred enlargement of a cell
    — proved for the frozen carrier in
   `WholeSpaceRowsCellContraction.lean`;
2. the neighbour covering, turning the contraction into a one-step decrease
   along the partition graph  — proved there as well;
3. the discrete maximum principle and the graph-sphere summation
    — proved in `WholeSpaceDecayGraph.lean`
   and `WholeSpaceDecayExterior.lean`;
4. the graph-distance cover of the Euclidean exterior and the random radius
    — the content,
   which is a geometric input to this assembly.

This file assembles 1–3 into a single statement about the frozen carrier whose
remaining hypotheses are *purely geometric and ellipticity data of the cells*:
sizes, centres, upper coefficient bounds on the enlargements, a neighbour
cover, sphere growth, and the exterior cover.  Nothing analytic is left.

The parameter `theta0` is the paper's `C eta`: `hsmall` is exactly
`t (size Q)⁻² Lam(Q̂) ≤ C⁻¹ eta`, with `Lam` the `L^∞` bound of the coefficient
on the enlargement.  The paper uses the *coarse-grained* `Lambda_{1/16}` instead of the pointwise upper coefficient bound.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open _root_.SubdiffusiveProcess.Section8
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The cell of a stopping family: the triadic cube of scale `scale j i`
centred at `centre j i`. -/
def stoppingCell {d : ℕ} {count : ℕ → ℕ}
    (scale : (j : ℕ) → Fin (count j) → ℤ)
    (centre : (j : ℕ) → Fin (count j) → Vec d)
    (j : ℕ) (i : Fin (count j)) : Set (Vec d) :=
  translatedCube d (scale j i) (centre j i)

/-- The centred threefold enlargement `Q̂` of a stopping cell. -/
def stoppingCellEnlargement {d : ℕ} {count : ℕ → ℕ}
    (scale : (j : ℕ) → Fin (count j) → ℤ)
    (centre : (j : ℕ) → Fin (count j) → Vec d)
    (j : ℕ) (i : Fin (count j)) : Set (Vec d) :=
  translatedCube d (scale j i + 1) (centre j i)

/-- **The exterior row, modulo the stopping partition.**

Let `u` be a whole-space divergence-resolvent solution.  Suppose a family of
triadic cells, graded by graph distance to the source family, satisfies:

* a source bound on the cells at distance `0`;
* off the source, the datum vanishes on each enlargement, the coefficient is
  bounded there by `Lam j i`, and the smallness condition
  `4096 d Lam t (3^{scale})⁻² ≤ theta0`;
* each enlargement is covered by at most `Nnbr` cells of graph level at least
  `j - 1`;
* graph spheres have at most `N D^j` cells;
* the exterior is covered by the spheres beyond `⌈rate⌉`.

Then the exterior `L²` mass decays geometrically in `rate`.

The only inputs are geometric; the analytic content is
`wholeSpaceSolution_cell_mass_contraction`.
-/
theorem wholeSpaceSolution_exterior_decay_of_stopping_cells
    {a f : Vec d → ℝ} {t : ℝ} (ht : 0 < t) (haNonneg : ∀ x, 0 ≤ a x)
    (u : WholeSpaceDivergenceResolventSolution a t f)
    {count : ℕ → ℕ}
    (scale : (j : ℕ) → Fin (count j) → ℤ)
    (centre : (j : ℕ) → Fin (count j) → Vec d)
    (lam Lam : (j : ℕ) → (i : Fin (count j)) → ℝ)
    (exterior : Set (Vec d)) {A theta0 : ℝ} (N D Nnbr : ℕ) {rate : ℝ}
    (hA : 0 ≤ A) (htheta0 : 0 < theta0) (hNnbr : 0 < Nnbr) (hD : 0 < D)
    (heffective : (D : ℝ) * ((Nnbr : ℝ) * theta0) < 1)
    (hsource : ∀ i : Fin (count 0),
      ∫ x in stoppingCell scale centre 0 i, u.toFun x ^ 2 ∂volume ≤ A)
    (hLamNonneg : ∀ (j : ℕ) (i : Fin (count j)), 0 ≤ Lam j i)
    (hell : ∀ (j : ℕ) (i : Fin (count j)), 0 < j →
      IsEllipticFieldOn (lam j i) (Lam j i)
        (stoppingCellEnlargement scale centre j i) (scalarCoeffField a))
    (habove : ∀ (j : ℕ) (i : Fin (count j)), 0 < j →
      ∀ x ∈ stoppingCellEnlargement scale centre j i, a x ≤ Lam j i)
    (hquiet : ∀ (j : ℕ) (i : Fin (count j)), 0 < j →
      ∀ x ∈ stoppingCellEnlargement scale centre j i, f x = 0)
    (hsmall : ∀ (j : ℕ) (i : Fin (count j)), 0 < j →
      4096 * (d : ℝ) * Lam j i * t * ((3 : ℝ) ^ scale j i)⁻¹ ^ 2 ≤ theta0)
    (hnbr : ∀ (j : ℕ) (i : Fin (count j)), 0 < j →
      ∃ s : Finset (Σ k : ℕ, Fin (count k)), s.Nonempty ∧ s.card ≤ Nnbr ∧
        (∀ p ∈ s, j ≤ p.1 + 1) ∧
        stoppingCellEnlargement scale centre j i ⊆
          ⋃ p ∈ s, stoppingCell scale centre p.1 p.2)
    (hcard : ∀ j, count j ≤ N * D ^ j)
    (hcover : exterior ⊆
      ⋃ p : Σ k : ℕ, Fin (count (⌈rate⌉₊ + k)),
        stoppingCell scale centre (⌈rate⌉₊ + p.1) p.2) :
    ∫ x in exterior, u.toFun x ^ 2 ∂volume ≤
      (N : ℝ) * A * (1 - (D : ℝ) * ((Nnbr : ℝ) * theta0))⁻¹ *
        Real.exp (Real.log ((D : ℝ) * ((Nnbr : ℝ) * theta0)) * rate) := by
  classical
  have hNnbrR : (0 : ℝ) < (Nnbr : ℝ) := by exact_mod_cast hNnbr
  refine integral_sq_exterior_le_of_graph_cells u.toFun u.memL2_toFun count
    (fun j i ↦ stoppingCell scale centre j i) exterior N D hA
    (by positivity) hD heffective hsource ?_ hcard hcover
  intro j i hj
  obtain ⟨s, hsne, hscard, hslevel, hscover⟩ := hnbr j i hj
  obtain ⟨p, hp, hple⟩ := exists_neighbour_cell_mass_contraction ht
    (hell j i hj) haNonneg (hLamNonneg j i) htheta0.le (habove j i hj) u
    (hquiet j i hj) (hsmall j i hj) s hsne
    (fun p ↦ stoppingCell scale centre p.1 p.2) hscover
  refine ⟨p, hslevel p hp, ?_⟩
  have hnn : 0 ≤ ∫ x in stoppingCell scale centre p.1 p.2,
      u.toFun x ^ 2 ∂volume :=
    setIntegral_nonneg
      (isOpenBoundedConvexDomain_translatedCube d (scale p.1 p.2)
        (centre p.1 p.2)).isOpen.measurableSet fun x _ ↦ sq_nonneg _
  refine hple.trans ?_
  have hcardR : (s.card : ℝ) ≤ (Nnbr : ℝ) := by exact_mod_cast hscard
  have : (s.card : ℝ) * theta0 ≤ (Nnbr : ℝ) * theta0 :=
    mul_le_mul_of_nonneg_right hcardR htheta0.le
  exact mul_le_mul_of_nonneg_right this hnn

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
