module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import MarkovProcess.Lifetime.ExitTimeStopping
public import MarkovProcess.Path.ExitTime

@[expose] public section

/-!
# Exit times from library cubes

This file specializes the continuous-path and lifetime-path exit-time vocabulary from
`MarkovProcess` to the centered and translated open cubes used by the GMC library.

The lifetime-path definitions are the ones compatible with the cemetery architecture of
Section 7: reaching the cemetery state counts as leaving every live cube.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

open Homogenization MarkovProcess MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ}

/-! ## Cube geometry -/

/-- A centered library cube is open. -/
theorem isOpen_cube (d : ℕ) (m : ℤ) : IsOpen (cube d m) :=
  Homogenization.isOpen_openCubeSet (originCube d m)

/-- A translated library cube is open. -/
theorem isOpen_translatedCube (d : ℕ) (m : ℤ) (z : Vec d) :
    IsOpen (translatedCube d m z) := by
  unfold translatedCube
  exact (Homeomorph.addLeft z).isOpenMap (cube d m) (isOpen_cube d m)

/-! ## Ordinary continuous paths -/

/-- The exit time of a continuous path from the centered library cube `cube d m`. -/
def cubeExitTime (d : ℕ) (m : ℤ) : ContinuousPath (Vec d) → ℝ≥0∞ :=
  ContinuousPath.exitTime (cube d m)

/-- The exit time from a translated library cube. -/
def translatedCubeExitTime (m : ℤ) (z : Vec d) : ContinuousPath (Vec d) → ℝ≥0∞ :=
  ContinuousPath.exitTime (translatedCube d m z)

/-- The centered-cube exit time in the `WithTop` form used by stopping-time APIs. -/
def cubeExitTimeTop (d : ℕ) (m : ℤ) : ContinuousPath (Vec d) → WithTop ℝ≥0 :=
  ContinuousPath.exitTimeTop (cube d m)

/-- The translated-cube exit time in the `WithTop` form used by stopping-time APIs. -/
def translatedCubeExitTimeTop (m : ℤ) (z : Vec d) :
    ContinuousPath (Vec d) → WithTop ℝ≥0 :=
  ContinuousPath.exitTimeTop (translatedCube d m z)

/-- The centered-cube exit time truncated at the deterministic horizon `K`. -/
def cubeExitTimeTrunc (d : ℕ) (m : ℤ) (K : ℝ≥0) :
    ContinuousPath (Vec d) → ℝ≥0 :=
  ContinuousPath.exitTimeTrunc (cube d m) K

/-- The translated-cube exit time truncated at the deterministic horizon `K`. -/
def translatedCubeExitTimeTrunc (m : ℤ) (z : Vec d) (K : ℝ≥0) :
    ContinuousPath (Vec d) → ℝ≥0 :=
  ContinuousPath.exitTimeTrunc (translatedCube d m z) K

@[simp]
theorem cubeExitTimeTop_apply (m : ℤ) (omega : ContinuousPath (Vec d)) :
    cubeExitTimeTop d m omega = cubeExitTime d m omega :=
  rfl

@[simp]
theorem translatedCubeExitTimeTop_apply (m : ℤ) (z : Vec d)
    (omega : ContinuousPath (Vec d)) :
    translatedCubeExitTimeTop m z omega = translatedCubeExitTime m z omega :=
  rfl

theorem coe_cubeExitTimeTrunc (m : ℤ) (K : ℝ≥0)
    (omega : ContinuousPath (Vec d)) :
    ((cubeExitTimeTrunc d m K omega : ℝ≥0) : WithTop ℝ≥0) =
      min (cubeExitTimeTop d m omega) (K : WithTop ℝ≥0) :=
  ContinuousPath.coe_exitTimeTrunc (cube d m) K omega

theorem coe_translatedCubeExitTimeTrunc (m : ℤ) (z : Vec d) (K : ℝ≥0)
    (omega : ContinuousPath (Vec d)) :
    ((translatedCubeExitTimeTrunc m z K omega : ℝ≥0) : WithTop ℝ≥0) =
      min (translatedCubeExitTimeTop m z omega) (K : WithTop ℝ≥0) :=
  ContinuousPath.coe_exitTimeTrunc (translatedCube d m z) K omega

theorem cubeExitTimeTrunc_le (m : ℤ) (K : ℝ≥0) (omega : ContinuousPath (Vec d)) :
    cubeExitTimeTrunc d m K omega ≤ K :=
  ContinuousPath.exitTimeTrunc_le (cube d m) K omega

theorem translatedCubeExitTimeTrunc_le (m : ℤ) (z : Vec d) (K : ℝ≥0)
    (omega : ContinuousPath (Vec d)) : translatedCubeExitTimeTrunc m z K omega ≤ K :=
  ContinuousPath.exitTimeTrunc_le (translatedCube d m z) K omega

/-- The exit time from a centered library cube is a stopping time. -/
theorem isStoppingTime_cubeExitTime (d : ℕ) (m : ℤ) :
    IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := Vec d))
      (cubeExitTimeTop d m) :=
  ContinuousPath.isStoppingTime_exitTime (cube d m) (isOpen_cube d m)

/-- The exit time from a translated library cube is a stopping time. -/
theorem isStoppingTime_translatedCubeExitTime (m : ℤ) (z : Vec d) :
    IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := Vec d))
      (translatedCubeExitTimeTop m z) :=
  ContinuousPath.isStoppingTime_exitTime (translatedCube d m z)
    (isOpen_translatedCube d m z)

/-- A centered-cube exit time truncated at `K` is a finite stopping time. -/
theorem isStoppingTime_cubeExitTimeTrunc (d : ℕ) (m : ℤ) (K : ℝ≥0) :
    IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun omega ↦ ((cubeExitTimeTrunc d m K omega : ℝ≥0) : WithTop ℝ≥0)) :=
  ContinuousPath.isStoppingTime_exitTimeTrunc (cube d m) (isOpen_cube d m) K

/-- A translated-cube exit time truncated at `K` is a finite stopping time. -/
theorem isStoppingTime_translatedCubeExitTimeTrunc (m : ℤ) (z : Vec d) (K : ℝ≥0) :
    IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun omega ↦
        ((translatedCubeExitTimeTrunc m z K omega : ℝ≥0) : WithTop ℝ≥0)) :=
  ContinuousPath.isStoppingTime_exitTimeTrunc (translatedCube d m z)
    (isOpen_translatedCube d m z) K

/-! ## Cemetery-compatible lifetime paths -/

/-- Exit from a centered library cube for a path with a lifetime. -/
def lifetimeCubeExitTime (d : ℕ) (m : ℤ) : LifetimePath (Vec d) → ℝ≥0∞ :=
  LifetimePath.exitTime (cube d m)

/-- Exit from a translated library cube for a path with a lifetime. -/
def lifetimeTranslatedCubeExitTime (m : ℤ) (z : Vec d) :
    LifetimePath (Vec d) → ℝ≥0∞ :=
  LifetimePath.exitTime (translatedCube d m z)

/-- Reaching the cemetery bounds the centered-cube exit time. -/
theorem lifetimeCubeExitTime_le_lifetime (m : ℤ) (omega : LifetimePath (Vec d)) :
    lifetimeCubeExitTime d m omega ≤ omega.lifetime :=
  LifetimePath.exitTime_le_lifetime (cube d m) omega

/-- Reaching the cemetery bounds the translated-cube exit time. -/
theorem lifetimeTranslatedCubeExitTime_le_lifetime (m : ℤ) (z : Vec d)
    (omega : LifetimePath (Vec d)) :
    lifetimeTranslatedCubeExitTime m z omega ≤ omega.lifetime :=
  LifetimePath.exitTime_le_lifetime (translatedCube d m z) omega

/-- The lifetime-path exit time from a centered cube is a stopping time. -/
theorem isStoppingTime_lifetimeCubeExitTime (d : ℕ) (m : ℤ) :
    IsStoppingTime (LifetimePath.canonicalFiltration (alpha := Vec d))
      (lifetimeCubeExitTime d m) :=
  LifetimePath.isStoppingTime_exitTime (cube d m) (isOpen_cube d m)

/-- The lifetime-path exit time from a translated cube is a stopping time. -/
theorem isStoppingTime_lifetimeTranslatedCubeExitTime (m : ℤ) (z : Vec d) :
    IsStoppingTime (LifetimePath.canonicalFiltration (alpha := Vec d))
      (lifetimeTranslatedCubeExitTime m z) :=
  LifetimePath.isStoppingTime_exitTime (translatedCube d m z)
    (isOpen_translatedCube d m z)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
