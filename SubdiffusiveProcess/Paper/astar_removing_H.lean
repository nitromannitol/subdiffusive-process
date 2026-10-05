module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The *Removing `H`* step of `mfd:lem-coercivity` (paper label `mfd:lem-coercivity`).

The physical field factors through the infrared potential.  In this project that is not an
assumption but a definition: `cutoffCoefficient M H om N x` is
`(â_N)⁻¹ exp(cutoffPotential H om N x − (N+1)τ²)` and `cutoffPotential H om N x` is
`H om x + ∑_{j ≤ N} ω_{−j}(x)`, so `A_N = e^{H(ω)} · a_N` with the native field `a_N`
written out on the right below.

The two properties of `a_*^{-1}` the step uses — nonincreasing in the coefficient, and
homogeneous of degree `−1` — are carried as hypotheses rather than assumed of a particular
carrier.  Their supplier is the variational formula `e.variational.a`, which
 carries as its `matrices` and `responseJ_split` fields.  `Hnorm` is a bound on
`‖H(ω)‖_∞`, whose moments come from `lem_infrared`.

Stated with the `â_N` factor where the project's definition puts it, inside the native
field, rather than pulled out in front as the paper writes it; the two differ only by where
the normalisation is carried. -/
theorem astar_removing_H :
  ∀ (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ)
    (astarInv : (SpatialCoordinates d → ℝ) → ℝ),
    -- `a_*^{-1}(U; ·)` is nonincreasing in the coefficient
    (∀ a b : SpatialCoordinates d → ℝ, (∀ x, 0 < a x) → (∀ x, a x ≤ b x) →
      astarInv b ≤ astarInv a) →
    -- and homogeneous of degree `-1`
    (∀ c : ℝ, 0 < c → ∀ a : SpatialCoordinates d → ℝ, (∀ x, 0 < a x) →
      astarInv (fun x => c * a x) = c⁻¹ * astarInv a) →
  ∀ Hnorm : ℝ, (∀ x, |H om x| ≤ Hnorm) →
    astarInv (fun x => cutoffCoefficient M H om N x) ≤
      Real.exp Hnorm *
        astarInv (fun x => (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
          Real.exp ((∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
            ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) := by
  intro d _ _ M H om N astarInv hmono hhom Hnorm hH
  set nat : SpatialCoordinates d → ℝ := fun x =>
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
      Real.exp ((∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
        ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) with hnat
  have hahom : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N :=
    SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hnatpos : ∀ x, 0 < nat x := by
    intro x
    rw [hnat]
    exact mul_pos (inv_pos.2 hahom) (Real.exp_pos _)
  -- the physical field factors as `e^{H} · nat`, by the two definitions
  have hfact : ∀ x, cutoffCoefficient M H om N x = Real.exp (H om x) * nat x := by
    intro x
    rw [cutoffCoefficient, cutoffPotential, hnat]
    rw [show (H om x + ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
        ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P =
        H om x + ((∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
          ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) from by ring,
      Real.exp_add]
    ring
  -- a pointwise lower bound with the constant `e^{-Hnorm}`
  have hlow : ∀ x, Real.exp (-Hnorm) * nat x ≤ cutoffCoefficient M H om N x := by
    intro x
    rw [hfact x]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.2 (by linarith [(abs_le.1 (hH x)).1])) (hnatpos x).le
  have hscalepos : (0 : ℝ) < Real.exp (-Hnorm) := Real.exp_pos _
  have hstep := hmono (fun x => Real.exp (-Hnorm) * nat x)
    (fun x => cutoffCoefficient M H om N x)
    (fun x => mul_pos hscalepos (hnatpos x)) hlow
  rw [hhom (Real.exp (-Hnorm)) hscalepos nat hnatpos] at hstep
  rw [Real.exp_neg, inv_inv] at hstep
  exact hstep

end SubdiffusiveProcess.Paper
