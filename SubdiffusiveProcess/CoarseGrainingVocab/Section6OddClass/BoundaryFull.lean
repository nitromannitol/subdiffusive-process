module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass.EvenBoundFinal
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass.Compose

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/ExcessDecay/OneStepBoundaryFull.lean
-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/OneStepBoundaryFull.lean

@[expose] public section

/-!
# The boundary branch with the datum leg folded into the excess leg

produced the boundary Schauder estimate with **two** legs, the second being the
odd-class defect refuted the reading of that second leg as the manuscript's
`[∇h]` leg and reduced it to the even-part bound `(★)`'s
`OneStepEvenBoundFinal` proves `(★)`.  This module collects the consequence.

## The producer

For a competitor **odd about the met face** and classically harmonic on the
doubled window, the gradient-Hölder producer has a single leg:

```text
  [∇V]_{C^{0,1/2}(U₃)} ≤ C(d) (3^{-n})^{1/2} E(V, U₂) ,
```

i.e. exactly the interior display, at the boundary, with no boundary-datum
contribution at all.  This is `exists_gradientHolder_boundary_faceOdd`.

## The endpoint

Feeding it to `OneStepConditional.excessDecay_oneStep_of_harmonicApprox` at
`K_h = 0` discharges the Schauder slot on the boundary branch and
gives the one-step contraction with only the two frozen legs — the excess leg
and the harmonic-approximation remainder:
`excessDecay_oneStep_boundary_faceOdd_of_harmonicApprox`.

## What is still an input, exactly

The competitor the manuscript's chain hands to this producer is **not** odd: it
is `v` with `v = h` on the met portion of `∂□_m`.  The reduction to an odd
competitor is `v = ℓ_h + V_odd + v₁` with `v₁` the datum corrector of
`OneStepDatumSplit` (whose `L^∞` size is `2 d [∇h]_{C^{0,1/2}(U₂)}
(3^{n-2}/2)^{3/2}`, proved there), and `V_odd = v - ℓ_h - v₁` carrying zero
data on the met face.  Turning `V_odd` into the doubled window's `H¹` datum
needs the **odd reflection across the met face** of a function whose trace
vanishes on that face only — not on all of `∂U₂`.  The missing input is
therefore a **face-only** zero-trace glue, i.e. a hyperplane trace-matching
theorem; this repository has no trace operator, and none is introduced here.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass

open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

open MeasureTheory InnerProductSpace
open Homogenization (Vec vecDot openCubeSet originCube coordFaceReflection)



noncomputable section

variable {d : ℕ}

/-- **The boundary producer at a face-odd competitor: one leg.**

`exists_gradientHolder_boundary_odd_ae` with the odd affine datum taken to be the
normal part of an affine minimizer, and the resulting odd-class defect folded
into the excess by `(★)`. -/
theorem exists_gradientHolder_boundary_faceOdd (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m n : ℤ) (x : Vec d) (i : Fin d) (V : Vec d → ℝ) (c : ℝ)
      (A : Vec d),
      x ∈ openCubeSet (originCube d m) → n - 2 < m →
      MeetsUpperFace x m (n - 2) i →
      (∀ j, j ≠ i → ¬ MeetsUpperFace x m (n - 2) j ∧ ¬ MeetsLowerFace x m (n - 2) j) →
      (∀ z, V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -V z) →
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) →
      MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))) →
      IsAffineMinimizer (truncatedWindow x m (n - 2)) V (c - vecDot A x) A →
      ∃ K : ℝ, 0 ≤ K ∧
        (∀ j, IntegrableOn (fun p => gradField V p j) (truncatedWindow x m (n - 3)) volume) ∧
        HasGradientOn (truncatedWindow x m (n - 3)) V (gradField V) ∧
        supHolderBoundOn (truncatedWindow x m (n - 3)) (1 / 2 : ℝ) K (gradField V) ∧
        K ≤ C * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
              * affineExcess (truncatedWindow x m (n - 2)) V := by
  obtain ⟨Cd, hCd0, hCd⟩ := exists_oddClassDefect_le_affineExcessRaw d
  refine ⟨(1 + Cd) * boundaryOddSchauderConst d,
    mul_nonneg (by linarith only [hCd0]) (boundaryOddSchauderConst_nonneg d), ?_⟩
  intro m n x i V c A hx hmn hup hother hVodd hharm hVR hmin
  have hVO : V =ᵐ[volume.restrict (reflectedWindow x m (n - 2))] fun y => V y + 0 := by
    filter_upwards with y
    ring
  have hOodd : oddExtend x m (n - 2) V
      =ᵐ[volume.restrict (reflectedWindow x m (n - 2))] V :=
    MeasureTheory.ae_restrict_of_ae
      (oddExtend_ae_eq_self_of_faceOdd_upper hup hother hVodd)
  have hodd : IsOddAffineData x m (n - 2) (oddAffineIntercept x m i A - 0)
      (oddAffineSlope i A) := by
    rw [sub_zero]
    exact isOddAffineData_oddAffineDatum hmn hup hother A
  obtain ⟨K, hK, hint, hgrad, hhol, hbound⟩ :=
    exists_gradientHolder_boundary_odd_ae hd hx hmn hVO hOodd hodd hharm hVR
  refine ⟨K, hK, hint, hgrad, hhol, le_trans hbound ?_⟩
  set kappa : ℝ := boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
    with hkappadef
  have hkappa0 : 0 ≤ kappa := by
    rw [hkappadef]
    exact mul_nonneg (boundaryOddSchauderConst_nonneg d)
      (Real.rpow_nonneg (zpow_pos (by norm_num) (-n)).le _)
  have hscale : (0 : ℝ) < (3 : ℝ) ^ (-(n - 2)) := zpow_pos (by norm_num) _
  have hnormz : (3 : ℝ) ^ (-(n - 2)) * affineExcessRaw (truncatedWindow x m (n - 2)) V
      ≤ affineExcess (truncatedWindow x m (n - 2)) V := by
    rw [affineExcess]
    exact mul_le_mul_of_nonneg_right
      (rpow_volume_truncatedWindow_bounds hd x hx (by omega)).1
      (affineExcessRaw_nonneg _ _)
  have hdefect := hCd m n x i V c A hx hmn hup hother hVodd hharm hVR hmin
  have hstep : (3 : ℝ) ^ (-(n - 2))
        * oddClassDefect x m n V (oddAffineIntercept x m i A) (oddAffineSlope i A)
      ≤ Cd * affineExcess (truncatedWindow x m (n - 2)) V := by
    calc (3 : ℝ) ^ (-(n - 2))
          * oddClassDefect x m n V (oddAffineIntercept x m i A) (oddAffineSlope i A)
        ≤ (3 : ℝ) ^ (-(n - 2)) * (Cd * affineExcessRaw (truncatedWindow x m (n - 2)) V) :=
          mul_le_mul_of_nonneg_left hdefect hscale.le
      _ = Cd * ((3 : ℝ) ^ (-(n - 2)) * affineExcessRaw (truncatedWindow x m (n - 2)) V) := by
          ring
      _ ≤ Cd * affineExcess (truncatedWindow x m (n - 2)) V :=
          mul_le_mul_of_nonneg_left hnormz hCd0
  have hfold : kappa * ((3 : ℝ) ^ (-(n - 2))
        * oddClassDefect x m n V (oddAffineIntercept x m i A) (oddAffineSlope i A))
      ≤ kappa * (Cd * affineExcess (truncatedWindow x m (n - 2)) V) :=
    mul_le_mul_of_nonneg_left hstep hkappa0
  have hrewrite : (1 + Cd) * boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
        * affineExcess (truncatedWindow x m (n - 2)) V
      = kappa * affineExcess (truncatedWindow x m (n - 2)) V
        + kappa * (Cd * affineExcess (truncatedWindow x m (n - 2)) V) := by
    rw [hkappadef]
    ring
  rw [hrewrite]
  linarith only [hfold]

/-! ## The corner regime is realized -/

/-- **The multi-met-face (corner) regime is not empty.**

For every `k < m` there is a centre `x ∈ □_m` whose window `(x + □_k) ∩ □_m`
meets the upper face of **every** coordinate at once.  In particular, in
dimension `d ≥ 2` the boundary branch's one-met-face hypothesis `hother` is a
genuine restriction of the covering, not a consequence of the geometry: the
excess-decay consumption, which must cover every `x ∈ □_m` whose window is not
interior, does meet corner windows.

This is the machine check the multi-face question needs.  The odd affine class
collapses to `{0}` at two met faces, so at a corner the odd-class pricing
degenerates and the two-face reflection group has to be run instead
(`OneStepOddMultiFace`); `(★)` as proved here is stated at one met face. -/
theorem exists_mem_openCubeSet_forall_meetsUpperFace {m k : ℤ} (hkm : k < m) :
    ∃ x : Vec d, x ∈ openCubeSet (originCube d m) ∧ ∀ l : Fin d, MeetsUpperFace x m k l := by
  have hk : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hlt : (3 : ℝ) ^ k < (3 : ℝ) ^ m := zpow_lt_zpow_right₀ (by norm_num) hkm
  refine ⟨fun _ => (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 4 : ℝ) * (3 : ℝ) ^ k, ?_, ?_⟩
  · rw [Homogenization.mem_openCubeSet_originCube_iff]
    intro l
    refine ⟨?_, ?_⟩
    · show -(1 / 2 : ℝ) * (3 : ℝ) ^ m
        < (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 4 : ℝ) * (3 : ℝ) ^ k
      linarith only [hlt, hk]
    · show (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 4 : ℝ) * (3 : ℝ) ^ k
        < (1 / 2 : ℝ) * (3 : ℝ) ^ m
      linarith only [hk]
  · intro l
    show (1 / 2 : ℝ) * (3 : ℝ) ^ m
      ≤ ((1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 4 : ℝ) * (3 : ℝ) ^ k) + (1 / 2 : ℝ) * (3 : ℝ) ^ k
    linarith only [hk]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass
