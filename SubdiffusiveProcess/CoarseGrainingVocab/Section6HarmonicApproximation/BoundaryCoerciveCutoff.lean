module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCoerciveEstimate
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAffineLift
public import Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalPatchCutoff

@[expose] public section

/-!
# Canonical-cutoff form of the direct boundary coercive estimate

This connects the direct test by `eta^2 (u-h)` to the local radius profile
used by CoarseGraining's Caccioppoli iteration.  The analytic integrability
premises remain explicit here; the next layer discharges them for the scalar
cutoff coefficient and prices the three right-hand-side densities.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The local energy profile is below the squared canonical-cutoff energy.
Unlike the library's linear-cutoff version, this is the exact lower bound
needed by the direct test `eta^2 (u-h)`. -/
theorem coarseCaccioppoliLocalEnergyProfile_le_boundaryCoerciveMain
    {Q : TriadicCube d} {center : Vec d} {rhoInner rhoOuter : ℝ}
    {a : Vec d → ℝ} {u : H1Function (openCubeSet Q)}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (ha : ∀ x ∈ cubeSet Q, 0 < a x)
    (henergy : IntegrableOn (fun x => a x * vecNormSq (u.grad x))
      (cubeSet Q))
    (hmain : IntegrableOn
      (boundaryCoerciveMainDensity a
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) u.grad)
      (cubeSet Q)) :
    coarseCaccioppoliLocalEnergyProfile Q center rhoInner
        (fun x => a x * vecNormSq (u.grad x)) ≤
      cubeAverage Q
        (boundaryCoerciveMainDensity a
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) u.grad) := by
  unfold coarseCaccioppoliLocalEnergyProfile
  apply cubeAverage_le_cubeAverage_of_le_on Q
    (integrableOn_indicator_coarseCaccioppoliLocalClosedCube_of_integrableOn_cubeSet
      Q center rhoInner henergy) hmain
  intro x hxQ
  by_cases hx : x ∈ coarseCaccioppoliLocalClosedCube Q center rhoInner
  · have heta := coarseCaccioppoliLocalCanonicalFun_eq_one_on_inner
      hinner hinnerOuter hx
    simp [Set.indicator_of_mem hx, boundaryCoerciveMainDensity, heta]
  · rw [Set.indicator_of_notMem hx]
    exact mul_nonneg
      (mul_nonneg (ha x hxQ).le (sq_nonneg _)) (vecNormSq_nonneg _)

/-- The direct nonzero-datum weak test, specialized to the canonical local
cutoff and normalized in the parent-cube average.  This is the exact input
shape for a radius recurrence. -/
theorem coarseCaccioppoliLocalEnergyProfile_le_boundaryCoerciveTerms
    {Q : TriadicCube d} {center : Vec d} {rhoInner rhoOuter : ℝ}
    {a : Vec d → ℝ} {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hdir : SubdiffusiveProcess.CoarseGrainingVocab.IsDirichletSolutionOn a Q u h g)
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (haOpen : ∀ x ∈ openCubeSet Q, 0 < a x)
    (haCube : ∀ x ∈ cubeSet Q, 0 < a x)
    (henergy : IntegrableOn (fun x => a x * vecNormSq (u.grad x))
      (cubeSet Q))
    (hmain : IntegrableOn
      (boundaryCoerciveMainDensity a
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) u.grad)
      (openCubeSet Q))
    (hweakLeft : IntegrableOn
      (boundaryCoerciveWeakLeftDensity a
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter)
        (fun y => u.toFun y - h.toFun y) u.grad h.grad) (openCubeSet Q))
    (hweakForce : IntegrableOn
      (boundaryCoerciveWeakForceDensity
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter)
        (fun y => u.toFun y - h.toFun y) u.grad h.grad g) (openCubeSet Q))
    (hrhs : IntegrableOn
      (boundaryCoerciveRhsDensity a
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter)
        (fun y => u.toFun y - h.toFun y) u.grad h.grad g) (openCubeSet Q))
    (hdatum : IntegrableOn
      (boundaryCoerciveDatumDensity a
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) h.grad)
      (openCubeSet Q))
    (hcutoff : IntegrableOn
      (boundaryCoerciveCutoffDensity a
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter)
        (fun y => u.toFun y - h.toFun y)) (openCubeSet Q))
    (hforce : IntegrableOn
      (boundaryCoerciveForceDensity a
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) g)
      (openCubeSet Q)) :
    coarseCaccioppoliLocalEnergyProfile Q center rhoInner
        (fun x => a x * vecNormSq (u.grad x)) ≤
      4 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity a
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) h.grad) +
        14 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveCutoffDensity a
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter)
            (fun y => u.toFun y - h.toFun y)) +
        8 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity a
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) g) := by
  let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter
  have hmainCube : IntegrableOn (boundaryCoerciveMainDensity a eta u.grad)
      (cubeSet Q) := by
    simpa only [IntegrableOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using hmain
  have hlower := coarseCaccioppoliLocalEnergyProfile_le_boundaryCoerciveMain
    hinner hinnerOuter haCube henergy hmainCube
  have hcoercive := setIntegral_boundaryCoerciveMain_le hdir
    (coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner hinnerOuter)
    (coarseCaccioppoliLocalCanonicalFun_hasCompactSupport Q center hinner hinnerOuter)
    haOpen hmain hweakLeft hweakForce hrhs hdatum hcutoff hforce
  rw [← volumeAverage_openCubeSet_eq_cubeAverage_local] at hlower
  unfold volumeAverage at hlower ⊢
  have hvol : 0 ≤ (volume (openCubeSet Q)).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hcoercive hvol
  exact hlower.trans (hscaled.trans_eq (by ring))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
