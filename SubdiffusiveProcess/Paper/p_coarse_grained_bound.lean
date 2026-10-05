module

public import SubdiffusiveProcess.Section4.CoarseGrainedBound

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Proposition `p.coarse.grained.bound` (self-similar coarse-graining estimate).

Correspondence with the live paper statement (paper label `e.homogenize.at.scale.m`, `p.coarse.grained.bound`):
* `c(d), C(d)` are chosen before the model `M` (a `GMCModel d`, i.e. Assumptions g1--g4 with parameter
  `M.delta`), the moment `ξ` and the scale `m`: dimension-only constants.
* `(e.xi.upper.bound.gmc)` is `ξ ≤ C⁻¹ * (δ²)⁻¹ * |log δ|⁻¹`.
* `(e.homogenize.at.scale.m)` is the `L^ξ(ℙ)` bound of `normalizedDefect M m (cu_m)`, the sphere maximum
  `max_{|e|=1} J(cu_m, ahom_m^{-1/2} e, ahom_m^{1/2} e; a_m)`.
* `(e.homogenize.at.scale.m.E)` is the `L^ξ(ℙ)` bound of `homogenizationErrorRandom M m m s`, i.e.
  `𝓔_{s,∞}(cu_m; a_m, ahom_m)` (omitted `q` means `q = 1`). -/
theorem p_coarse_grained_bound {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (ξ : ℝ),
        1 ≤ ξ →
        ξ ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        ∀ m : ℕ,
          paperENNRealLpNorm M.P.toMeasure ξ
              (normalizedDefect M m
                (Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)))) ≤
            ENNReal.ofReal (C * ξ * Real.log (2 + ξ) * M.delta ^ 2) ∧
          ∀ s : ℝ, 0 < s → s ≤ 1 →
            4 * (d : ℝ) * s⁻¹ ≤ ξ →
            C * ξ * Real.log (2 + ξ) * M.delta ^ 2 ≤ c * s →
            c ≤ s * Real.log (2 + ξ) →
            paperENNRealLpNorm M.P.toMeasure ξ
                (homogenizationErrorRandom M m m s) ≤
              ENNReal.ofReal
                (C * s⁻¹ * Real.sqrt (ξ * Real.log (2 + ξ) * M.delta ^ 2))
    := _root_.SubdiffusiveProcess.Section4.coarse_grained_bound

end SubdiffusiveProcess.Paper
