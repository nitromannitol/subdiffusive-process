module

public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Lane3.Forms
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.grid_points_near_integers

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Fine step of `mfd:lem-shifts`: the boundary-strip residue geometry, which
is what makes the union bound of `shift_union_bound` say anything about the
shifted grid.

`pos x i n` is the position of coordinate `i` of `x` inside its depth-`n`
parent, in units of the child side `L^{-n}`, so the shift by `r/M` moves it to
`pos x i n + r/M`.  `hbadmem` is the DEFINITION of a bad residue -- the shifted
position lies within `(w+1)/L` of an integer -- and `hnonPadded` the
DEFINITION of a non-padded child, that some coordinate is bad.

The two conclusions are the geometry the lemma needs: the count of bad
residues per coordinate, `2((w+1)M/L + 1)`, obtained because the bad set is
two intervals of length `(w+1)/L` per period and the residues are spaced
`1/M` apart; and the identification of the non-padded children with the
shifts having a bad coordinate. -/
theorem shift_strip_residues
    (d Mm : ℕ) (hd : 1 ≤ d) (hM : 2 ≤ Mm) (L : ℝ) (hL : 2 ≤ L)
    (w : ℝ) (hw : 0 ≤ w)
    (pos : (Fin d → ℝ) → Fin d → ℕ → ℝ)
    (badOf : ℕ → (Fin d → ℝ) → Fin d → Finset (Fin Mm))
    (nonPadded : (Fin d → Fin Mm) → ℕ → (Fin d → ℝ) → Prop)
    (hbadmem : ∀ (n : ℕ) (x : Fin d → ℝ) (i : Fin d) (r : Fin Mm),
      r ∈ badOf n x i ↔
        ∃ k : ℤ, |pos x i n + (r : ℕ) / (Mm : ℝ) - (k : ℝ)| ≤ (w + 1) / L)
    (hnonPadded : ∀ (s : Fin d → Fin Mm) (n : ℕ) (x : Fin d → ℝ),
      nonPadded s n x ↔ ∃ i : Fin d, s i ∈ badOf n x i) :
    (∀ (n : ℕ) (x : Fin d → ℝ) (i : Fin d),
        ((badOf n x i).card : ℝ) ≤ 2 * ((w + 1) * (Mm : ℝ) / L + 1)) ∧
      ∀ (s : Fin d → Fin Mm) (n : ℕ) (x : Fin d → ℝ),
        nonPadded s n x ↔ ∃ i : Fin d, s i ∈ badOf n x i := by
  refine ⟨?_, hnonPadded⟩
  intro n x i
  have hL0 : (0:ℝ) < L := by linarith
  have hMpos : 0 < Mm := by omega
  have hdelta : (0:ℝ) ≤ (w + 1) / L := by positivity
  have hkey := grid_points_near_integers Mm hMpos (pos x i n) ((w + 1) / L)
    hdelta (badOf n x i) (fun r => hbadmem n x i r)
  have hrw : (w + 1) / L * (Mm : ℝ) = (w + 1) * (Mm : ℝ) / L := by
    field_simp
  rw [hrw] at hkey
  exact hkey

end Paper
