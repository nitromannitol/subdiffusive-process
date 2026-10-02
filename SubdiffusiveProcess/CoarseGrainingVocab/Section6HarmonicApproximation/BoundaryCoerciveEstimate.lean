import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCoerciveDensities

/-!
# Integrated direct boundary coercive estimate

The weak Dirichlet identity is converted here into the scalar energy estimate
with nonzero boundary datum.  The theorem deliberately exposes only
integrability premises; the geometric cutoff and coefficient bounds belong to
the subsequent radius-iteration layer.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

theorem setIntegral_boundaryCoerciveMain_eq_rhs
    {V : Set (Vec d)} {a eta w : Vec d → ℝ}
    {U H G : Vec d → Vec d}
    (hmain : IntegrableOn (boundaryCoerciveMainDensity a eta U) V)
    (hweakLeft : IntegrableOn (boundaryCoerciveWeakLeftDensity a eta w U H) V)
    (hweakForce : IntegrableOn (boundaryCoerciveWeakForceDensity eta w U H G) V)
    (hrhs : IntegrableOn (boundaryCoerciveRhsDensity a eta w U H G) V)
    (hweak :
      ∫ x in V, boundaryCoerciveWeakLeftDensity a eta w U H x ∂volume =
        -∫ x in V, boundaryCoerciveWeakForceDensity eta w U H G x ∂volume) :
    ∫ x in V, boundaryCoerciveMainDensity a eta U x ∂volume =
      ∫ x in V, boundaryCoerciveRhsDensity a eta w U H G x ∂volume := by
  have hpoint :
      (fun x => boundaryCoerciveMainDensity a eta U x -
          boundaryCoerciveWeakLeftDensity a eta w U H x) =
        fun x => boundaryCoerciveRhsDensity a eta w U H G x +
          boundaryCoerciveWeakForceDensity eta w U H G x := by
    funext x
    rw [boundaryCoercive_main_sub_weakLeft,
      boundaryCoercive_rhs_add_weakForce]
  have hint :
      ∫ x in V, (boundaryCoerciveMainDensity a eta U x -
          boundaryCoerciveWeakLeftDensity a eta w U H x) ∂volume =
        ∫ x in V, (boundaryCoerciveRhsDensity a eta w U H G x +
          boundaryCoerciveWeakForceDensity eta w U H G x) ∂volume := by
    rw [hpoint]
  rw [integral_sub hmain hweakLeft, integral_add hrhs hweakForce] at hint
  linarith only [hint, hweak]

/-- The weak identity from `IsDirichletSolutionOn`, expressed in the density
notation used by the coercive estimate. -/
theorem setIntegral_boundaryCoerciveWeak_identity
    {Q : TriadicCube d} {a : Vec d → ℝ}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hdir : IsDirichletSolutionOn a Q u h g)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) :
    ∫ x in openCubeSet Q,
        boundaryCoerciveWeakLeftDensity a eta
          (fun y => u.toFun y - h.toFun y) u.grad h.grad x ∂volume =
      -∫ x in openCubeSet Q,
        boundaryCoerciveWeakForceDensity eta
          (fun y => u.toFun y - h.toFun y) u.grad h.grad g x ∂volume := by
  simpa only [boundaryCoerciveWeakLeftDensity,
    boundaryCoerciveWeakForceDensity, boundarySqCutoffTestGradient] using
    setIntegral_boundarySqCutoffTestGradient_identity hdir heta hetaCompact

/-- Direct boundary coercivity from an already-constructed squared-cutoff
weak identity.  This form is shared by the full-trace and localized-trace
carriers. -/
theorem setIntegral_boundaryCoerciveMain_le_of_weak_identity
    {Q : TriadicCube d} {a eta : Vec d → ℝ}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (ha : ∀ x ∈ openCubeSet Q, 0 < a x)
    (hmain : IntegrableOn (boundaryCoerciveMainDensity a eta u.grad)
      (openCubeSet Q))
    (hweakLeft : IntegrableOn
      (boundaryCoerciveWeakLeftDensity a eta
        (fun y => u.toFun y - h.toFun y) u.grad h.grad) (openCubeSet Q))
    (hweakForce : IntegrableOn
      (boundaryCoerciveWeakForceDensity eta
        (fun y => u.toFun y - h.toFun y) u.grad h.grad g) (openCubeSet Q))
    (hrhs : IntegrableOn
      (boundaryCoerciveRhsDensity a eta
        (fun y => u.toFun y - h.toFun y) u.grad h.grad g) (openCubeSet Q))
    (hdatum : IntegrableOn (boundaryCoerciveDatumDensity a eta h.grad)
      (openCubeSet Q))
    (hcutoff : IntegrableOn
      (boundaryCoerciveCutoffDensity a eta
        (fun y => u.toFun y - h.toFun y)) (openCubeSet Q))
    (hforce : IntegrableOn (boundaryCoerciveForceDensity a eta g)
      (openCubeSet Q))
    (hweak :
      ∫ x in openCubeSet Q,
          boundaryCoerciveWeakLeftDensity a eta
            (fun y => u.toFun y - h.toFun y) u.grad h.grad x ∂volume =
        -∫ x in openCubeSet Q,
          boundaryCoerciveWeakForceDensity eta
            (fun y => u.toFun y - h.toFun y) u.grad h.grad g x ∂volume) :
    ∫ x in openCubeSet Q, boundaryCoerciveMainDensity a eta u.grad x ∂volume ≤
      4 * ∫ x in openCubeSet Q,
          boundaryCoerciveDatumDensity a eta h.grad x ∂volume +
        14 * ∫ x in openCubeSet Q,
          boundaryCoerciveCutoffDensity a eta
            (fun y => u.toFun y - h.toFun y) x ∂volume +
        8 * ∫ x in openCubeSet Q,
          boundaryCoerciveForceDensity a eta g x ∂volume := by
  let w : Vec d → ℝ := fun y => u.toFun y - h.toFun y
  have hid := setIntegral_boundaryCoerciveMain_eq_rhs
    hmain hweakLeft hweakForce hrhs hweak
  have hpoint :
      boundaryCoerciveRhsDensity a eta w u.grad h.grad g
        ≤ᵐ[volume.restrict (openCubeSet Q)]
        fun x => (3 / 8 : ℝ) * boundaryCoerciveMainDensity a eta u.grad x +
          (5 / 2 : ℝ) * boundaryCoerciveDatumDensity a eta h.grad x +
          (17 / 2 : ℝ) * boundaryCoerciveCutoffDensity a eta w x +
          (9 / 2 : ℝ) * boundaryCoerciveForceDensity a eta g x := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact boundaryCoerciveRhsDensity_le (ha x hx)
  have hcutoff0 :
      0 ≤ ∫ x in openCubeSet Q, boundaryCoerciveCutoffDensity a eta w x ∂volume :=
    integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
      exact boundaryCoerciveCutoffDensity_nonneg (ha x hx).le)
  have hforce0 :
      0 ≤ ∫ x in openCubeSet Q, boundaryCoerciveForceDensity a eta g x ∂volume :=
    integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
      exact boundaryCoerciveForceDensity_nonneg (ha x hx).le)
  exact setIntegral_boundary_coercive_absorb hmain hrhs hdatum hcutoff hforce
    hcutoff0 hforce0 hid hpoint

/-- Direct nonzero-datum boundary coercivity after the squared-cutoff weak
test.  This is the analytic replacement for the zero-boundary-only public
Caccioppoli wrapper. -/
theorem setIntegral_boundaryCoerciveMain_le
    {Q : TriadicCube d} {a eta : Vec d → ℝ}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hdir : IsDirichletSolutionOn a Q u h g)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetaCompact : HasCompactSupport eta)
    (ha : ∀ x ∈ openCubeSet Q, 0 < a x)
    (hmain : IntegrableOn (boundaryCoerciveMainDensity a eta u.grad)
      (openCubeSet Q))
    (hweakLeft : IntegrableOn
      (boundaryCoerciveWeakLeftDensity a eta
        (fun y => u.toFun y - h.toFun y) u.grad h.grad) (openCubeSet Q))
    (hweakForce : IntegrableOn
      (boundaryCoerciveWeakForceDensity eta
        (fun y => u.toFun y - h.toFun y) u.grad h.grad g) (openCubeSet Q))
    (hrhs : IntegrableOn
      (boundaryCoerciveRhsDensity a eta
        (fun y => u.toFun y - h.toFun y) u.grad h.grad g) (openCubeSet Q))
    (hdatum : IntegrableOn (boundaryCoerciveDatumDensity a eta h.grad)
      (openCubeSet Q))
    (hcutoff : IntegrableOn
      (boundaryCoerciveCutoffDensity a eta
        (fun y => u.toFun y - h.toFun y)) (openCubeSet Q))
    (hforce : IntegrableOn (boundaryCoerciveForceDensity a eta g)
      (openCubeSet Q)) :
    ∫ x in openCubeSet Q, boundaryCoerciveMainDensity a eta u.grad x ∂volume ≤
      4 * ∫ x in openCubeSet Q,
          boundaryCoerciveDatumDensity a eta h.grad x ∂volume +
        14 * ∫ x in openCubeSet Q,
          boundaryCoerciveCutoffDensity a eta
            (fun y => u.toFun y - h.toFun y) x ∂volume +
      8 * ∫ x in openCubeSet Q,
          boundaryCoerciveForceDensity a eta g x ∂volume := by
  exact setIntegral_boundaryCoerciveMain_le_of_weak_identity ha hmain hweakLeft
    hweakForce hrhs hdatum hcutoff hforce
      (setIntegral_boundaryCoerciveWeak_identity hdir heta hetaCompact)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
