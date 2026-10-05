module

public import Mathlib
public import MarkovProcess.Path.Basic

@[expose] public section

open MeasureTheory
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Continuous paths in a finite real coordinate space; compact-open topology. -/
abbrev FiniteRealPath (d : ℕ) := C(ℝ≥0, Fin d → ℝ)

def centeredScale {d : ℕ} (a : ℝ) (c : ℝ≥0)
    (w : FiniteRealPath d) : FiniteRealPath d :=
  ⟨fun t => a • (w (c * t) - w 0), by fun_prop⟩

def linearImagePath {d e : ℕ} (L : (Fin d → ℝ) →L[ℝ] (Fin e → ℝ))
    (w : FiniteRealPath d) : FiniteRealPath e :=
  ⟨fun t => L (w t), L.continuous.comp w.continuous⟩

theorem measurable_centeredScale {d : ℕ} (a : ℝ) (c : ℝ≥0) :
    Measurable (centeredScale (d := d) a c) := by
  apply Continuous.measurable
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous fun p : FiniteRealPath d × ℝ≥0 =>
    a • (p.1 (c * p.2) - p.1 0)
  fun_prop

theorem measurable_linearImagePath {d e : ℕ}
    (L : (Fin d → ℝ) →L[ℝ] (Fin e → ℝ)) :
    Measurable (linearImagePath L) := by
  exact (ContinuousMap.continuous_postcomp ⟨L, L.continuous⟩).measurable

theorem centeredScale_linearImagePath {d e : ℕ}
    (L : (Fin d → ℝ) →L[ℝ] (Fin e → ℝ))
    (a : ℝ) (c : ℝ≥0) (w : FiniteRealPath d) :
    centeredScale a c (linearImagePath L w) =
      linearImagePath L (centeredScale a c w) := by
  ext t i
  simp [centeredScale, linearImagePath, map_smul, map_sub]

/-- Scaling equality of path measures passes through every finite linear image,
including singular and zero maps. This does not assume a Brownian consumer carrier. -/
theorem map_centeredScale_linearImage {d e : ℕ}
    (Q : Measure (FiniteRealPath d))
    (L : (Fin d → ℝ) →L[ℝ] (Fin e → ℝ)) (a : ℝ) (c : ℝ≥0)
    (hscale : Q.map (centeredScale a c) = Q.map (centeredScale 1 1)) :
    (Q.map (linearImagePath L)).map (centeredScale a c) =
      (Q.map (linearImagePath L)).map (centeredScale 1 1) := by
  rw [Measure.map_map (measurable_centeredScale a c) (measurable_linearImagePath L),
    Measure.map_map (measurable_centeredScale 1 1) (measurable_linearImagePath L)]
  have hcomm : ∀ b s, centeredScale (d := e) b s ∘ linearImagePath L =
      linearImagePath L ∘ centeredScale (d := d) b s := by
    intro b s
    funext w
    exact centeredScale_linearImagePath L b s w
  rw [hcomm a c, hcomm 1 1,
    ← Measure.map_map (measurable_linearImagePath L) (measurable_centeredScale a c),
    ← Measure.map_map (measurable_linearImagePath L) (measurable_centeredScale 1 1), hscale]

/-- The zero covariance branch is the zero continuous path law. -/
theorem centeredScale_zero (d : ℕ) (a : ℝ) (c : ℝ≥0) :
    centeredScale a c (0 : FiniteRealPath d) = 0 := by
  ext t i
  simp [centeredScale]


end SubdiffusiveProcess.Section10
