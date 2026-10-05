module

public import SubdiffusiveProcess.Geometry.OddGrid
public import SubdiffusiveProcess.Geometry.OddGridResidual
public import Mathlib.Tactic

@[expose] public section

/-!
# The `L`-adic subdivision tree and its face strips, `L = 3 ^ H₁`

paper label `mfd:lem-shifts` fixes a subdivision factor
`L = 3^{H_1}` (paper label `mfd:lem-shifts`) and
subdivides a root cube into `L^d` children at each step.  Taking `L` a power
of three is a specialization of a free parameter that the paper only requires
to be large (paper label `mfd:lem-shifts`, 3600), so the existing odd grid of this
project realizes it exactly: with `2 m + 1 = 3 ^ H₁` the cell
`oddGridCell z r hr m k` is the `L`-adic child of the cube of centre `z` and
side `r` with label `k`.

* `SubdiffusiveProcess.ResponseMoments.subdivisionHalfWidth H₁` is that `m`.
* `SubdiffusiveProcess.ResponseMoments.descendantCenter` / `SubdiffusiveProcess.ResponseMoments.descendantSide` / `SubdiffusiveProcess.ResponseMoments.descendantCell`
  are the depth-`n` descendant along a word of labels; `descendantCell` at
  depth `0` is the root cube.
* `SubdiffusiveProcess.ResponseMoments.oddGridStrip z r m wid` is the set of points within `wid` of a cell
  face of the odd grid of `(z, r, m)` — the "strips" of Lemma
  `mfd:lem-strips`, paper label `mfd:lem-shifts`, as a thin slab around the midplanes of
  `Geometry/OddGrid`.

No statement in this file asserts a conclusion of the paper.
-/

open Set TopologicalSpace

noncomputable section

namespace SubdiffusiveProcess
namespace ResponseMoments

variable {d : ℕ}

/-- The odd-grid half-width realizing the subdivision factor `L = 3 ^ H₁`. -/
def subdivisionHalfWidth (H1 : ℕ) : ℕ := (3 ^ H1 - 1) / 2

/-- Side length of the depth-`n` descendant of a cube of side `r`. -/
def descendantSide (m n : ℕ) (r : ℝ) : ℝ := r / (2 * (m : ℝ) + 1) ^ n

theorem descendantSide_pos (m n : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < descendantSide m n r := by
  unfold descendantSide
  positivity

theorem descendantSide_zero (m : ℕ) (r : ℝ) : descendantSide m 0 r = r := by
  simp [descendantSide]

theorem descendantSide_succ (m n : ℕ) (r : ℝ) :
    descendantSide m (n + 1) r = descendantSide m n r / (2 * (m : ℝ) + 1) := by
  have hpos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  unfold descendantSide
  rw [pow_succ, div_div]

/-- Centre of the depth-`n` descendant along the word of labels `w`. -/
def descendantCenter (m : ℕ) (z : SpatialCoordinates d) (r : ℝ) :
    (n : ℕ) → (Fin n → OddGridIndex d m) → SpatialCoordinates d
  | 0, _ => z
  | (n + 1), w =>
      oddGridCenter (descendantCenter m z r n fun i => w i.castSucc)
        (descendantSide m n r) m (w (Fin.last n))

/-- The depth-`n` descendant cell of the root cube of centre `z` and side `r`. -/
def descendantCell (m : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (n : ℕ) (w : Fin n → OddGridIndex d m) : Opens (SpatialCoordinates d) :=
  centeredCube (descendantCenter m z r n w) (descendantSide m n r)
    (descendantSide_pos m n hr)

/-- Points within `wid` of a cell face of the odd grid of `(z, r, m)`:
the strips of Lemma `mfd:lem-strips`, paper label `mfd:lem-strips`. -/
def oddGridStrip (z : SpatialCoordinates d) (r : ℝ) (m : ℕ) (wid : ℝ) :
    Set (SpatialCoordinates d) :=
  {x | ∃ (i : Fin d) (t : ℤ),
    |x i - (z i + ((t : ℝ) + 1 / 2) * (r / (2 * (m : ℝ) + 1)))| ≤ wid}


theorem two_mul_subdivisionHalfWidth_add_one (H1 : ℕ) :
    2 * subdivisionHalfWidth H1 + 1 = 3 ^ H1 := by
  have h : Odd (3 ^ H1) := Odd.pow (by decide)
  obtain ⟨k, hk⟩ := h
  unfold subdivisionHalfWidth
  omega

theorem descendantCell_coe (m : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (n : ℕ) (w : Fin n → OddGridIndex d m) :
    (descendantCell m z hr n w : Set (SpatialCoordinates d)) =
      Metric.ball (descendantCenter m z r n w) (descendantSide m n r / 2) := rfl

theorem descendantCell_succ_subset (m : ℕ) (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (n : ℕ) (w : Fin (n + 1) → OddGridIndex d m) :
    (descendantCell m z hr (n + 1) w : Set (SpatialCoordinates d)) ⊆
      (descendantCell m z hr n (fun i => w i.castSucc) : Set (SpatialCoordinates d)) := by
  have hsub := oddGridCell_subset
    (descendantCenter m z r n fun i => w i.castSucc)
    (descendantSide_pos m n hr) m (w (Fin.last n))
  have hcoe : (oddGridCell (descendantCenter m z r n fun i => w i.castSucc)
      (descendantSide m n r) (descendantSide_pos m n hr) m (w (Fin.last n)) :
        Set (SpatialCoordinates d)) =
      (descendantCell m z hr (n + 1) w : Set (SpatialCoordinates d)) := by
    rw [descendantCell_coe]
    change Metric.ball _ ((descendantSide m n r / (2 * (m : ℝ) + 1)) / 2) = _
    rw [← descendantSide_succ]
    rfl
  rw [← hcoe, descendantCell_coe]
  exact hsub


/-- One-dimensional lattice index range for a cover of a slab of thickness
`2 wid` inside a cube of side `rt` by sup-metric balls of radius `wid`. -/
def slabCoverRange (rt wid : ℝ) : Finset ℤ :=
  Finset.Icc (-⌈rt / wid⌉ - 1) (⌈rt / wid⌉ + 1)

/-- The lattice of centres covering the slab `{x | |x i - c| ≤ wid}` inside the
cube of centre `z` and side `rt`: the `i`-th coordinate is pinned to `c`, the
others run over `slabCoverRange`. -/
def slabCoverIndex (i : Fin d) (rt wid : ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun j => if j = i then ({0} : Finset ℤ) else slabCoverRange rt wid

/-- The centre of the cover ball with lattice label `k`. -/
def slabCoverCenter (z : SpatialCoordinates d) (i : Fin d) (c wid : ℝ)
    (k : Fin d → ℤ) : SpatialCoordinates d :=
  fun j => if j = i then c else z j + (k j : ℝ) * wid

/-- The slab of half-thickness `wid` about the hyperplane `x i = c`. -/
def coordinateSlab (i : Fin d) (c wid : ℝ) : Set (SpatialCoordinates d) :=
  {x | |x i - c| ≤ wid}

theorem oddGridStrip_eq_iUnion (z : SpatialCoordinates d) (r : ℝ) (m : ℕ)
    (wid : ℝ) :
    oddGridStrip z r m wid =
      ⋃ (i : Fin d) (t : ℤ),
        coordinateSlab i (z i + ((t : ℝ) + 1 / 2) * (r / (2 * (m : ℝ) + 1))) wid := by
  ext x
  simp only [oddGridStrip, coordinateSlab, Set.mem_ofPred_eq, Set.mem_iUnion]


theorem oddGridCell_coe (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (m : ℕ)
    (k : OddGridIndex d m) :
    (oddGridCell z r hr m k : Set (SpatialCoordinates d)) =
      Metric.ball (oddGridCenter z r m k) (r / (2 * (m : ℝ) + 1) / 2) := rfl

/-- The lattice label of a point for the slab cover: pinned at `i`, the nearest
lattice point in every other coordinate. -/
def slabCoverLabel (z : SpatialCoordinates d) (i : Fin d) (wid : ℝ)
    (x : SpatialCoordinates d) : Fin d → ℤ :=
  fun j => if j = i then 0 else round ((x j - z j) / wid)

end ResponseMoments
end SubdiffusiveProcess
