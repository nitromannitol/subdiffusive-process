module

public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The three estimates of Lemma `tight:lem-static` for a speed density `b` and coefficient `A`
on the reference cube `Metric.ball 0 (rho0 / 2)` (sup-norm balls are cubes), with constant `K`
and deterministic exponent `B`:
1. mass bounds `K⁻¹ r^{d+1/2} ≤ μ(B_r(x)) ≤ K r^{d-1/2}`, `μ = b dx`, for balls of radius
   `r ≤ 1` inside the reference cube;
2. `H^{3/4}` coercivity `‖v‖²_{H^{3/4}(V)} ≤ K' (E(v;V) + ‖v‖²_{L²(V)})` (and without the
   `L²` term on `H¹₀(V)`) on the countable nested family of concentric cubes `V` of rational
   relative side `q`, with `K' = K · den(q)^B` (constants growing at most as a fixed power of
   the reciprocal gap);
3. cutoffs `χ` between two concentric cubes of the family with gap `a`, `0 ≤ χ ≤ 1`, `χ = 1`
   on the smaller cube, vanishing near the boundary of the larger one, and
   `Γ_χ(B_r(x)) = ∫_{B_r(x)} A|∇χ|² ≤ K a^{-B} r^{d-1/2}` for `0 < r ≤ 1`.
All integrals of nonnegative quantities are lower Lebesgue integrals, so no integrability
side condition can make a clause vacuous. -/
def tight_static_estimates {d : ℕ} (b A : SpatialCoordinates d → ℝ) (rho0 K B : ℝ) : Prop :=
  (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
      Metric.ball x r ⊆ Metric.ball (0 : SpatialCoordinates d) (rho0 / 2) →
      ENNReal.ofReal (K⁻¹ * r ^ ((d : ℝ) + 1 / 2)) ≤
          volume.withDensity (fun z => ENNReal.ofReal (b z)) (Metric.ball x r) ∧
        volume.withDensity (fun z => ENNReal.ofReal (b z)) (Metric.ball x r) ≤
          ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2))) ∧
  (∀ q : ℚ, 0 < q → q ≤ 1 →
      (∀ v : Homogenization.H1Function
            (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q : ℝ) / 2)),
        (∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q : ℝ) / 2),
            ∫⁻ z in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q : ℝ) / 2),
              ENNReal.ofReal ((v.toFun x - v.toFun z) ^ 2) /
                ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
          ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q : ℝ) / 2),
            ENNReal.ofReal (v.toFun x ^ 2) ≤
        ENNReal.ofReal (K * (q.den : ℝ) ^ B) *
          ((∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q : ℝ) / 2),
              ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x))) +
            ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q : ℝ) / 2),
              ENNReal.ofReal (v.toFun x ^ 2))) ∧
      (∀ v : Homogenization.H10Function
            (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q : ℝ) / 2)),
        (∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q : ℝ) / 2),
            ∫⁻ z in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q : ℝ) / 2),
              ENNReal.ofReal ((v.toFun x - v.toFun z) ^ 2) /
                ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
          ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q : ℝ) / 2),
            ENNReal.ofReal (v.toFun x ^ 2) ≤
        ENNReal.ofReal (K * (q.den : ℝ) ^ B) *
          ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q : ℝ) / 2),
            ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x)))) ∧
  (∀ q1 q2 : ℚ, 0 < q1 → q1 < q2 → q2 ≤ 1 →
      ∃ chi : Homogenization.H10Function
          (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2)),
        (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
        (∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (rho0 * (q1 : ℝ) / 2), chi.toFun x = 1) ∧
        tsupport chi.toFun ⊆ Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2) ∧
        ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
          ∫⁻ z in Metric.ball x r ∩ Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2),
              ENNReal.ofReal (A z * Homogenization.vecDot (chi.grad z) (chi.grad z)) ≤
            ENNReal.ofReal (K * (rho0 * ((q2 : ℝ) - q1) / 2) ^ (-B) * r ^ ((d : ℝ) - 1 / 2)))

end Paper
