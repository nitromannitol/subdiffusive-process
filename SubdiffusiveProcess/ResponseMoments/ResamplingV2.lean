module

public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# The resampling carrier with Assumption `a.g1`

The
`fine_layer_influence` (L3-B1) is false because `SubdiffusiveProcess.ResponseMoments.ResamplingData` does
not carry the input the proof of `mfd:lem-15` cites at
`eq:mfd-15`:

> "The cores are at mutual distance `≥ Cr > √d 3^{-j}`, so by
> Assumption `a.g1` the restrictions `ξ_i = g_{-j}|_{B_i}` are mutually
> independent."

`ResamplingDataV2` is `ResamplingData` together with exactly that input and
the minimum needed to state it: the layer field itself, its dependence on one
coordinate only, its appearance in the cutoff potential, and the
identification of the moment bank's `S` with the layer sup norms.  Nothing
else is added.
-/

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess
namespace ResponseMoments

variable {d : ℕ}

/-- A potential restricted to a measurable set and extended by zero: the
carrier for `ξ_i = g_{-j}|_{B_i}`. -/
def restrictPotential {Q : Opens (SpatialCoordinates d)}
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s) (g : Potential Q) :
    Potential Q :=
  ((Lp.memLp g).indicator hs).toLp (Set.indicator s (fun x => g x))

/-- The hypothesis bundle of Lemma `mfd:lem-15` **with** Assumption `a.g1`
`scale` carries the `ε^{-2}`; take
`scale = 1` for `mfd:lem-15` itself. -/
structure ResamplingDataV2 (d : ℕ) (Q : Opens (SpatialCoordinates d))
    (Y : ℤ → Type) [instY : ∀ j, MeasurableSpace (Y j)]
    (laws : (j : ℤ) → Measure (Y j)) [instP : ∀ j, IsProbabilityMeasure (laws j)]
    (t p B : ℝ) (Cb : ℝ → ℕ → ℝ → ℝ → ℝ) (scale disorder : ℝ) where
  /-- The response. -/
  R : Response Q
  /-- `h N` is the potential `h_N - log κ_N` at ultraviolet cutoff `N`. -/
  h : ℕ → ((j : ℤ) → Y j) → Potential Q
  /-- The layer field `g_{-j}` restricted to `Q`. -/
  layer : ℤ → ((j : ℤ) → Y j) → Potential Q
  /-- `K N` is the constant of `eq:mfd-4` for the minimizer at cutoff `N`. -/
  K : ℕ → ((j : ℤ) → Y j) → ℝ
  /-- `S j` is the layer sup norm `‖g_{-j}‖_{L^∞(Q)}`. -/
  S : ℤ → ((j : ℤ) → Y j) → ℝ
  t_lower : (d : ℝ) - 1 < t
  t_upper : t < (d : ℝ)
  p_ge : 2 ≤ p
  B_nonneg : 0 ≤ B
  scale_pos : 0 < scale
  scale_le_one : scale ≤ 1
  disorder_pos : 0 < disorder
  disorder_le_one : disorder ≤ 1
  bank : LayerNormBank (Measure.infinitePi laws) Cb S disorder
  /-- The bank's `S` is the layer sup norm. -/
  S_eq : ∀ (j : ℤ) (ω : (j : ℤ) → Y j), S j ω = ‖layer j ω‖
  /-- Each layer depends on its own coordinate only. -/
  layer_coord : ∀ (j k : ℤ), j ≠ k → ∀ (ω : (j : ℤ) → Y j) (y : Y k),
    layer j (Function.update ω k y) = layer j ω
  /-- Replacing one layer changes the cutoff potential by that layer only. -/
  h_update : ∀ (N j : ℕ), j ≤ N → ∀ (ω : (j : ℤ) → Y j) (y : Y (-(j : ℤ))),
    h N (Function.update ω (-(j : ℤ)) y) =
      h N ω - layer (-(j : ℤ)) ω + layer (-(j : ℤ)) (Function.update ω (-(j : ℤ)) y)
  /-- **Assumption `a.g1`, **: the restrictions of one layer to
  finitely many sets at mutual distance greater than the layer's wavelength
  are mutually independent. -/
  spatial_indep : ∀ (j n : ℕ) (Bx : Fin n → Set (SpatialCoordinates d))
    (hBx : ∀ i, MeasurableSet (Bx i)),
    (∀ i i' : Fin n, i ≠ i' → ∀ x ∈ Bx i, ∀ y ∈ Bx i',
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℝ)) < dist x y) →
    iIndep (fun i : Fin n => MeasurableSpace.comap
      (fun ω => restrictPotential (hBx i) (layer (-(j : ℤ)) ω))
      (borel (Potential Q))) (Measure.infinitePi laws)
  /-- `eq:mfd-4` on `Q` with constant `K N / scale^2`. -/
  growth : ∀ (N : ℕ) (ω : (j : ℤ) → Y j) (x : SpatialCoordinates d) (r : ℝ),
    0 < r → r ≤ 1 →
    R.mass (h N ω) (Metric.ball x r) ≤ (K N ω / scale ^ 2) * r ^ t
  K_nonneg : ∀ N ω, 0 ≤ K N ω
  K_measurable : ∀ N, Measurable (K N)
  response_measurable : ∀ N, Measurable (fun ω => R.eval (h N ω))
  /-- `sup_N ‖K_N‖_{L^{3p}} ≤ B`. -/
  K_moment : ∀ N, eLpNorm (K N) (ENNReal.ofReal (3 * p))
    (Measure.infinitePi laws) ≤ ENNReal.ofReal B
  /-- `sup_N ‖𝓡_N‖_{L^{3p}} ≤ B`. -/
  response_moment : ∀ N, eLpNorm (fun ω => R.eval (h N ω)) (ENNReal.ofReal (3 * p))
    (Measure.infinitePi laws) ≤ ENNReal.ofReal B

end ResponseMoments
end SubdiffusiveProcess
