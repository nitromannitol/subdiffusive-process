module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass.Fold
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.BoundaryInterface




@[expose] public section

/-!
# The boundary Schauder endpoint in the section 6 carriers, with no additive leg

`Seam.exists_gradientHolder_boundary_metSet` is the odd-class fold's endpoint in
the Schauder argument's own carriers: at *every* met configuration — one met face,
either orientation, or any corner/edge — the gradient-Hölder seminorm of a
face-odd classically harmonic competitor is bounded by the excess alone,

```text
  K ≤ C(d) · (3^{-n})^{1/2} · E(V, U_{m,n-2}(x)) ,
```

with **no** boundary-datum term.  The odd-class defect that
`Section6Schauder.exists_gradientHolder_boundary_odd_truncatedCube` carries as
`schauderBoundaryOddDatum` has been priced *by the excess* and folded into the
excess leg (`EvenBoundFinal`'s `(★)`, `TransportFace`'s lower twin, and
`Transport`'s orientation-free corner `(★★)`).

This module performs the same three translations as
`Section6Schauder.BoundaryInterface` — the scale offset `n-2 ⟶ n`, the
normalizer `affineExcess ⟶ excess`, and the Hölder carrier
`supHolderBoundOn ⟶ HolderSeminormBoundOn` — so that the conclusion is exactly
the `hschauder` slot of
`SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.excess_oneStep_of_schauder` and of
`Section6BoundaryL2.excess_oneStep_boundary_datumSplit_l2`, **at `KhS = 0`**.

Consequently the `taylorConst d · (3^{n-k})^{1/2} · KhS` line of the one-step
conclusion is identically `0`, and the boundary branch of
`l.excess.decay.good.scales.GMC` no longer carries an unpriced additive leg.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass

open MeasureTheory InnerProductSpace
open Homogenization (Vec vecDot openCubeSet originCube coordFaceReflection)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

noncomputable section

variable {d : ℕ}

/-- **The boundary Schauder endpoint in the section 6 carriers, no additive
leg.**

For `V` odd about every met face of `∂□_m` at every point of the doubled window
`reflectedWindow x m (n-4)`, classically harmonic there, square integrable
there, and `(c,A)` an affine minimizer for `V` on `U_{m,n-4}(x)`, the gradient
field `gradField V` realizes the four slots `hint / hgrad / hhol / hschauder` of
`SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.excess_oneStep_of_schauder` with

```text
  Csch = C(d) ,   K_h = 0 .
```

The met set is arbitrary but nonempty; on the unmet (interior) branch the
interior producer applies instead. -/
theorem exists_gradientHolder_boundary_metSet_truncatedCube (d : ℕ) [NeZero d]
    (hd : d ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m n : ℤ) (x : Vec d) (i : Fin d) (V : Vec d → ℝ) (c : ℝ)
      (A : Vec d),
      x ∈ cube d m → n - 4 < m →
      (MeetsUpperFace x m (n - 4) i ∨ MeetsLowerFace x m (n - 4) i) →
      (∀ l : Fin d, MeetsUpperFace x m (n - 4) l →
        ∀ y ∈ reflectedWindow x m (n - 4),
          V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) →
      (∀ l : Fin d, MeetsLowerFace x m (n - 4) l →
        ∀ y ∈ reflectedWindow x m (n - 4),
          V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) →
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 4)) →
      MemLp V 2 (volume.restrict (reflectedWindow x m (n - 4))) →
      IsAffineMinimizer (truncatedCube d m (n - 4) x) V (c - vecDot A x) A →
      ∃ K : ℝ, 0 ≤ K ∧
        (∀ l, IntegrableOn (fun p => gradField V p l)
          (truncatedCube d m (n - 5) x) volume) ∧
        HasGradientOn (truncatedCube d m (n - 5) x) V (gradField V) ∧
        HolderSeminormBoundOn (truncatedCube d m (n - 5) x) (1 / 2 : ℝ) K
          (gradField V) ∧
        K ≤ C * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) *
              excess (n - 4) (truncatedCube d m (n - 4) x) V := by
  obtain ⟨C0, hC00, hC0⟩ := exists_gradientHolder_boundary_metSet d hd
  refine ⟨27 * (d : ℝ) * C0,
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hC00, ?_⟩
  intro m n x i V c A hx hmn hmet hupV hlowV hharm hVR hmin
  have h42 : n - 2 - 2 = n - 4 := by ring
  have h53 : n - 2 - 3 = n - 5 := by ring
  obtain ⟨K, hK0, hint, hgrad, hhol, hbound⟩ :=
    hC0 m (n - 2) x i V c A hx (by omega : n - 2 - 2 < m)
      (by rw [h42]; exact hmet)
      (by rw [h42]; exact hupV) (by rw [h42]; exact hlowV)
      (by rw [h42]; exact hharm) (by rw [h42]; exact hVR)
      (by rw [truncatedWindow_eq, h42]; exact hmin)
  rw [truncatedWindow_eq, h42] at hbound
  rw [truncatedWindow_eq, h53] at hint hgrad hhol
  refine ⟨(d : ℝ) * K, mul_nonneg (Nat.cast_nonneg d) hK0, hint, hgrad,
    holderSeminormBoundOn_of_supHolderBoundOn hK0 (by norm_num) hhol, ?_⟩
  set W : Set (Vec d) := truncatedCube d m (n - 4) x with hW
  set P : ℝ := ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg (by positivity) _
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hnorm : affineExcess W V ≤ 9 * excess (n - 4) W V :=
    affineExcess_le_excess_truncatedCube hd hx (by omega) V
  have hoff : ((3 : ℝ) ^ (-(n - 2))) ^ (1 / 2 : ℝ) = 3 * P := three_rpow_half_offset n
  rw [hoff] at hbound
  have hcoef : (0 : ℝ) ≤ C0 * (3 * P) := by positivity
  have hstep : C0 * (3 * P) * affineExcess W V ≤ C0 * (3 * P) * (9 * excess (n - 4) W V) :=
    mul_le_mul_of_nonneg_left hnorm hcoef
  calc (d : ℝ) * K
      ≤ (d : ℝ) * (C0 * (3 * P) * affineExcess W V) :=
        mul_le_mul_of_nonneg_left hbound hd0
    _ ≤ (d : ℝ) * (C0 * (3 * P) * (9 * excess (n - 4) W V)) :=
        mul_le_mul_of_nonneg_left hstep hd0
    _ = 27 * (d : ℝ) * C0 * P * excess (n - 4) W V := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass
