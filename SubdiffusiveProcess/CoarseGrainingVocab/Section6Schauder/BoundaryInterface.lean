module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.BoundaryDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.BoundaryOdd
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Interface




@[expose] public section

/-!
# The flat-face Schauder estimate in the section 6 vocabulary

`BoundaryDatum.exists_gradientHolder_boundary_split` delivers the flat-face
Schauder estimate in the Schauder argument's own carriers.  This module performs the
same three translations as `Interface` — the scale offset `n-2 ⟶ n`, the
normalizer `affineExcess ⟶ excess`, and the Hölder carrier
`supHolderBoundOn ⟶ HolderSeminormBoundOn` — so that the conclusion is exactly
the `hschauder` slot of
`SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.excess_oneStep_of_schauder`, with a
*nonzero* boundary leg `K_h`.

## What `K_h` is here, and what it is not

The leg produced is
`schauderBoundaryDatum`, built from
`boundaryDatumLeg x m (n-2) V c g = ‖V - ℓ‖_{L̲²(reflected ∖ U_{m,n-4}(x))}`:
the far-side (reflected) `L̲²` distance of the *odd extension* `V` to the affine
minimizer `ℓ = ℓ(V, U_{m,n-4}(x))`.  It vanishes identically when no face is met
(`boundaryDatumLeg_of_unmet`), which is the Lean reading of the manuscript's
indicator `1_∂`.

It is **not** the manuscript's `C[∇h]_{C^{0,1/2}(U_{m,n-4})}`.  Getting that
form requires the boundary datum `h` to enter, i.e. the *non-zero-trace* odd
reflection; what is proved here is the zero-trace argument, in which `V` is the odd
extension of the competitor across the met face and the datum shows up only
through its own far-side `L̲²` size.  

## Scope

The **one-met-face** regime: `hharm` asks for classical harmonicity on the
doubled window `reflectedWindow x m (n-4)`, which
`BoundaryComposition.exists_classicalCompetitor_reflectedWindow_of_meetsUpperFace`
(and its lower twin) supplies from variational harmonicity on the window itself
plus the `H¹` packaging of the odd extension.  Several met faces are not
covered.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

open MeasureTheory InnerProductSpace
open Homogenization (Vec openCubeSet originCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ### The constant and the leg -/

/-- **The flat-face Schauder constant section 6 reads.** -/
def schauderBoundaryConst (d : ℕ) [NeZero d] : ℝ := 27 * (d : ℝ) * boundarySchauderConst d

theorem schauderBoundaryConst_nonneg (d : ℕ) [NeZero d] : 0 ≤ schauderBoundaryConst d :=
  mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) (boundarySchauderConst_nonneg d)

/-- **The boundary leg `K_h` section 6 reads**: the far-side `L̲²` distance of the
odd extension to the affine minimizer on the window, with the argument's prefactor
carried through the three translations. -/
def schauderBoundaryDatum (d : ℕ) [NeZero d] (m n : ℤ) (x : Vec d) (V : Vec d → ℝ)
    (c : ℝ) (g : Vec d) : ℝ :=
  3 * (d : ℝ) * boundarySchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) *
    ((3 : ℝ) ^ (-(n - 4)) * boundaryDatumLeg x m (n - 2) V c g)

theorem schauderBoundaryDatum_nonneg (d : ℕ) [NeZero d] (m n : ℤ) (x : Vec d) (V : Vec d → ℝ)
    (c : ℝ) (g : Vec d) : 0 ≤ schauderBoundaryDatum d m n x V c g := by
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
    (boundarySchauderConst_nonneg d)) (Real.rpow_nonneg (by positivity) _)) ?_
  exact mul_nonneg (by positivity) (boundaryDatumLeg_nonneg x m (n - 2) V c g)

/-- On the interior branch — no met face — the boundary leg vanishes. -/
theorem schauderBoundaryDatum_of_unmet [NeZero d] {m n : ℤ} {x : Vec d}
    (hnone : ∀ i, ¬ MeetsUpperFace x m (n - 4) i ∧ ¬ MeetsLowerFace x m (n - 4) i)
    (V : Vec d → ℝ) (c : ℝ) (g : Vec d) :
    schauderBoundaryDatum d m n x V c g = 0 := by
  have h42 : n - 2 - 2 = n - 4 := by ring
  rw [schauderBoundaryDatum,
    boundaryDatumLeg_of_unmet (by rw [h42]; exact hnone), mul_zero, mul_zero]

/-! ### The estimate section 6 reads -/

/-- **The Schauder gradient-Hölder estimate up to a flat face, in the section 6
carriers.**

For `V` classically harmonic on the doubled window `reflectedWindow x m (n-4)`
and `(c,g)` an affine minimizer for `V` on `U_{m,n-4}(x)`, the gradient field
`gradField V` realizes the four slots `hint / hgrad / hhol / hschauder` of
`SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.excess_oneStep_of_schauder`, with

```text
  Csch = schauderBoundaryConst d ,   K_h = schauderBoundaryDatum d m n x V c g .
```
-/
theorem exists_gradientHolder_boundary_truncatedCube [NeZero d] (hd : d ≠ 0) {m n : ℤ}
    {x : Vec d} (hx : x ∈ cube d m) (hmn : n - 4 < m)
    {V : Vec d → ℝ}
    (hharm : HarmonicOnNhd (V ∘ toEuc.symm)
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 4)))
    (hintsq : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun y => (V y - affineEval c g y) ^ 2)
        (reflectedWindow x m (n - 4)) volume)
    {c : ℝ} {g : Vec d} (hmin : IsAffineMinimizer (truncatedCube d m (n - 4) x) V c g) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ i, IntegrableOn (fun p => gradField V p i) (truncatedCube d m (n - 5) x) volume) ∧
      HasGradientOn (truncatedCube d m (n - 5) x) V (gradField V) ∧
      HolderSeminormBoundOn (truncatedCube d m (n - 5) x) (1 / 2 : ℝ) K (gradField V) ∧
      K ≤ schauderBoundaryConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) *
            excess (n - 4) (truncatedCube d m (n - 4) x) V
          + schauderBoundaryDatum d m n x V c g := by
  have h42 : n - 2 - 2 = n - 4 := by ring
  have h53 : n - 2 - 3 = n - 5 := by ring
  obtain ⟨K, hK0, hint, hgrad, hhol, hbound⟩ :=
    exists_gradientHolder_boundary_split (d := d) (m := m) (n := n - 2) (x := x) hd hx
      (by omega : n - 2 - 2 < m) (V := V) (by rw [h42]; exact hharm)
      (fun c' g' => by rw [h42]; exact hintsq c' g')
      (c := c) (g := g) (by rw [truncatedWindow_eq, h42]; exact hmin)
  rw [truncatedWindow_eq, h42] at hbound
  rw [truncatedWindow_eq, h53] at hint hgrad hhol
  refine ⟨(d : ℝ) * K, mul_nonneg (Nat.cast_nonneg d) hK0, hint, hgrad,
    holderSeminormBoundOn_of_supHolderBoundOn hK0 (by norm_num) hhol, ?_⟩
  set W : Set (Vec d) := truncatedCube d m (n - 4) x with hW
  set P : ℝ := ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) with hP
  set Leg : ℝ := boundaryDatumLeg x m (n - 2) V c g with hLeg
  have hLeg0 : 0 ≤ Leg := boundaryDatumLeg_nonneg x m (n - 2) V c g
  have hP0 : 0 ≤ P := Real.rpow_nonneg (by positivity) _
  have hCsb : 0 ≤ boundarySchauderConst d := boundarySchauderConst_nonneg d
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hnorm : affineExcess W V ≤ 9 * excess (n - 4) W V :=
    affineExcess_le_excess_truncatedCube hd hx (by omega) V
  have hoff : ((3 : ℝ) ^ (-(n - 2))) ^ (1 / 2 : ℝ) = 3 * P := three_rpow_half_offset n
  rw [hoff] at hbound
  have hcoef : (0 : ℝ) ≤ boundarySchauderConst d * (3 * P) := by positivity
  have hstep : boundarySchauderConst d * (3 * P) * affineExcess W V
      ≤ boundarySchauderConst d * (3 * P) * (9 * excess (n - 4) W V) :=
    mul_le_mul_of_nonneg_left hnorm hcoef
  calc (d : ℝ) * K
      ≤ (d : ℝ) * (boundarySchauderConst d * (3 * P) * affineExcess W V
          + boundarySchauderConst d * (3 * P) * ((3 : ℝ) ^ (-(n - 4)) * Leg)) :=
        mul_le_mul_of_nonneg_left hbound hd0
    _ ≤ (d : ℝ) * (boundarySchauderConst d * (3 * P) * (9 * excess (n - 4) W V)
          + boundarySchauderConst d * (3 * P) * ((3 : ℝ) ^ (-(n - 4)) * Leg)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hstep]) hd0
    _ = schauderBoundaryConst d * P * excess (n - 4) W V
          + schauderBoundaryDatum d m n x V c g := by
        rw [schauderBoundaryConst, schauderBoundaryDatum, ← hP, ← hLeg]
        ring

/-! ### The odd-class pricing of the same estimate -/

/-- **The flat-face Schauder constant through the odd affine class.** -/
def schauderBoundaryOddConst (d : ℕ) [NeZero d] : ℝ := 27 * (d : ℝ) * boundaryOddSchauderConst d

theorem schauderBoundaryOddConst_nonneg (d : ℕ) [NeZero d] : 0 ≤ schauderBoundaryOddConst d :=
  mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) (boundaryOddSchauderConst_nonneg d)

/-- **The odd-class boundary leg `K_h`**: the amount by which restricting the
affine competitor to the odd class degrades the excess minimum on
`U_{m,n-4}(x)`.  It is `0` whenever the odd-class datum is an unrestricted
minimizer — in particular on the interior branch, where the odd class is the
whole affine class. -/
def schauderBoundaryOddDatum (d : ℕ) [NeZero d] (m n : ℤ) (x : Vec d) (V : Vec d → ℝ)
    (c : ℝ) (A : Vec d) : ℝ :=
  3 * (d : ℝ) * boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) *
    ((3 : ℝ) ^ (-(n - 4)) * oddClassDefect x m (n - 2) V c A)

theorem schauderBoundaryOddDatum_nonneg (d : ℕ) [NeZero d] (m n : ℤ) (x : Vec d)
    (V : Vec d → ℝ) (c : ℝ) (A : Vec d) : 0 ≤ schauderBoundaryOddDatum d m n x V c A := by
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
    (boundaryOddSchauderConst_nonneg d)) (Real.rpow_nonneg (by positivity) _)) ?_
  exact mul_nonneg (by positivity) (oddClassDefect_nonneg x m (n - 2) V c A)

/-- The odd-class leg vanishes at an unrestricted affine minimizer. -/
theorem schauderBoundaryOddDatum_of_isAffineMinimizer [NeZero d] {m n : ℤ} {x : Vec d}
    {V : Vec d → ℝ} {c : ℝ} {A : Vec d}
    (hmin : IsAffineMinimizer (truncatedCube d m (n - 4) x) V (c - Homogenization.vecDot A x) A) :
    schauderBoundaryOddDatum d m n x V c A = 0 := by
  have h42 : n - 2 - 2 = n - 4 := by ring
  rw [schauderBoundaryOddDatum,
    oddClassDefect_of_isAffineMinimizer (by rw [truncatedWindow_eq, h42]; exact hmin),
    mul_zero, mul_zero]

/-- **The Schauder gradient-Hölder estimate up to a flat face, odd-class pricing,
in the section 6 carriers.**

For an odd competitor `V` (`oddExtend x m (n-4) V = V`) classically harmonic on
the doubled window and an odd affine datum `(c,A)`, the gradient field realizes
the four slots of
`SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.excess_oneStep_of_schauder` with

```text
  Csch = schauderBoundaryOddConst d ,  K_h = schauderBoundaryOddDatum d m n x V c A .
```
-/
theorem exists_gradientHolder_boundary_odd_truncatedCube [NeZero d] (hd : d ≠ 0) {m n : ℤ}
    {x : Vec d} (hx : x ∈ cube d m) (hmn : n - 4 < m)
    {V : Vec d → ℝ} (hVodd : oddExtend x m (n - 4) V = V)
    {c : ℝ} {A : Vec d} (hodd : IsOddAffineData x m (n - 4) c A)
    (hharm : HarmonicOnNhd (V ∘ toEuc.symm)
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 4)))
    (hVR : MemLp V 2 (volume.restrict (reflectedWindow x m (n - 4)))) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ i, IntegrableOn (fun p => gradField V p i) (truncatedCube d m (n - 5) x) volume) ∧
      HasGradientOn (truncatedCube d m (n - 5) x) V (gradField V) ∧
      HolderSeminormBoundOn (truncatedCube d m (n - 5) x) (1 / 2 : ℝ) K (gradField V) ∧
      K ≤ schauderBoundaryOddConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) *
            excess (n - 4) (truncatedCube d m (n - 4) x) V
          + schauderBoundaryOddDatum d m n x V c A := by
  have h42 : n - 2 - 2 = n - 4 := by ring
  have h53 : n - 2 - 3 = n - 5 := by ring
  obtain ⟨K, hK0, hint, hgrad, hhol, hbound⟩ :=
    exists_gradientHolder_boundary_odd (d := d) (m := m) (n := n - 2) (x := x) hd hx
      (by omega : n - 2 - 2 < m) (V := V) (by rw [h42]; exact hVodd)
      (c := c) (A := A) (by rw [h42]; exact hodd) (by rw [h42]; exact hharm)
      (by rw [h42]; exact hVR)
  rw [truncatedWindow_eq, h42] at hbound
  rw [truncatedWindow_eq, h53] at hint hgrad hhol
  refine ⟨(d : ℝ) * K, mul_nonneg (Nat.cast_nonneg d) hK0, hint, hgrad,
    holderSeminormBoundOn_of_supHolderBoundOn hK0 (by norm_num) hhol, ?_⟩
  set W : Set (Vec d) := truncatedCube d m (n - 4) x with hW
  set P : ℝ := ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) with hP
  set Def : ℝ := oddClassDefect x m (n - 2) V c A with hDef
  have hDef0 : 0 ≤ Def := oddClassDefect_nonneg x m (n - 2) V c A
  have hP0 : 0 ≤ P := Real.rpow_nonneg (by positivity) _
  have hCsb : 0 ≤ boundaryOddSchauderConst d := boundaryOddSchauderConst_nonneg d
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hnorm : affineExcess W V ≤ 9 * excess (n - 4) W V :=
    affineExcess_le_excess_truncatedCube hd hx (by omega) V
  have hoff : ((3 : ℝ) ^ (-(n - 2))) ^ (1 / 2 : ℝ) = 3 * P := three_rpow_half_offset n
  rw [hoff] at hbound
  have hcoef : (0 : ℝ) ≤ boundaryOddSchauderConst d * (3 * P) := by positivity
  have hstep : boundaryOddSchauderConst d * (3 * P) * affineExcess W V
      ≤ boundaryOddSchauderConst d * (3 * P) * (9 * excess (n - 4) W V) :=
    mul_le_mul_of_nonneg_left hnorm hcoef
  calc (d : ℝ) * K
      ≤ (d : ℝ) * (boundaryOddSchauderConst d * (3 * P) * affineExcess W V
          + boundaryOddSchauderConst d * (3 * P) * ((3 : ℝ) ^ (-(n - 4)) * Def)) :=
        mul_le_mul_of_nonneg_left hbound hd0
    _ ≤ (d : ℝ) * (boundaryOddSchauderConst d * (3 * P) * (9 * excess (n - 4) W V)
          + boundaryOddSchauderConst d * (3 * P) * ((3 : ℝ) ^ (-(n - 4)) * Def)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hstep]) hd0
    _ = schauderBoundaryOddConst d * P * excess (n - 4) W V
          + schauderBoundaryOddDatum d m n x V c A := by
        rw [schauderBoundaryOddConst, schauderBoundaryOddDatum, ← hP, ← hDef]
        ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
