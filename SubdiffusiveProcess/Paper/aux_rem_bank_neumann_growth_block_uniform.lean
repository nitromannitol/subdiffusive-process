module

public import SubdiffusiveProcess.Paper.rem_bank
public import SubdiffusiveProcess.Paper.prop_neumann_growth_uniform

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Model-uniform twin of `aux_rem_bank_neumann_growth_block` (`rem_bank`,
the `eq:mfd-13` clause of `rem_bank`, `eq:mfd-13`): the `eps^-2` all-radii Neumann
constant `K13` with its order-`3p` moments, on the common full-measure event, from
`prop_neumann_growth_uniform`. Same conclusion as the frozen block, with the moment bound `B13`
chosen once, right after `(rho, pvec)` and before `∀ M`, instead of the frozen block's own
per-model choice (there, made together with `rho, pvec`, after `∀ M`) -- mirroring
`prop_neumann_growth_uniform`'s own reordering exactly one layer up. -/
theorem aux_rem_bank_neumann_growth_block_uniform (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : _root_.SubdiffusiveProcess.Paper.in_J d) (P : _root_.SubdiffusiveProcess.Paper.in_poincare d hd E) (X : _root_.SubdiffusiveProcess.Paper.in_extension d hd E)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (t : ℝ) (ht0 : (d : ℝ) - 1 < t) (ht1 : t < (d : ℝ)) (p : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ (2 ≤ p →
      ∀ rho : ℝ → ℝ, ContDiff ℝ ∞ rho → (∀ v : ℝ, 0 ≤ rho v) →
        (∀ v : ℝ, v ∉ Set.Ioo (1 : ℝ) 2 → rho v = 0) → (∫ v, rho v) = 1 →
        ∀ pvec : Fin d → ℝ, (∑ i : Fin d, (pvec i) ^ 2) = 1 →
      ∃ B13 : ℝ, 0 ≤ B13 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M) (Sreg : in_6_16 d M)
        (It : in_iteration d M E Sreg) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ →
      ∃ K13 : ℕ → BilateralField d → ℝ,
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N, 0 ≤ K13 N omega ∧
          (∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
            ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
            SolvesNeumann (cutoffPositiveCoefficient M H omega N
                (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) (faceBump rho pvec eps) v →
            ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ rad : ℝ,
              0 < rad → rad ≤ 1 →
              localGradientEnergy (cutoffPositiveCoefficient M H omega N
                  (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
                (show MeasurableSet (Metric.ball x rad ∩
                    (unitNeumannCube d : Set (SpatialCoordinates d))) from
                  (Metric.isOpen_ball.inter (unitNeumannCube d).isOpen).measurableSet)
                (sobolevGradient v.val) ≤
                K13 N omega * eps ^ (-2 : ℝ) * rad ^ t)) ∧
        (∀ N, MemLp (K13 N) (ENNReal.ofReal (3 * p)) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (K13 N) (ENNReal.ofReal (3 * p)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal B13)) := by
  by_cases hp : 2 ≤ p
  swap
  · exact ⟨1, one_pos, fun h => absurd h hp⟩
  obtain ⟨δ, hδ, hmain⟩ := prop_neumann_growth_uniform d hd E P X W D t 1 (fun _ => 3 * p) ht0 ht1
    (fun _ => by linarith)
  refine ⟨δ, hδ, fun _ rho hrho hrho0 hrhos hrhoi pvec hpvec => ?_⟩
  obtain ⟨Cb, hmain2⟩ := hmain rho hrho hrho0 hrhos hrhoi pvec hpvec
  refine ⟨max 0 (Cb 0), le_max_left _ _, fun M Rm Sreg It H hIC hle => ?_⟩
  obtain ⟨K, hKmem, hKnorm, hae⟩ := hmain2 M Rm Sreg It H hIC hle
  refine ⟨fun N omega => |K N omega|, ?_, ?_⟩
  · filter_upwards [hae] with omega hom N
    refine ⟨abs_nonneg _, fun eps heps heps8 v hv x hx rad hrad0 hrad1 => ?_⟩
    have h := hom N eps heps heps8 v hv x rad hx hrad0 hrad1
    refine h.trans ?_
    have hnn : 0 ≤ eps ^ (-2 : ℝ) * rad ^ t :=
      mul_nonneg (Real.rpow_nonneg heps.le _) (Real.rpow_nonneg hrad0.le _)
    calc K N omega * eps ^ (-2 : ℝ) * rad ^ t
        = K N omega * (eps ^ (-2 : ℝ) * rad ^ t) := by ring
      _ ≤ |K N omega| * (eps ^ (-2 : ℝ) * rad ^ t) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hnn
      _ = |K N omega| * eps ^ (-2 : ℝ) * rad ^ t := by ring
  · intro N
    exact aux_rem_bank_abs_moment _ (K N) (ENNReal.ofReal (3 * p)) (max 0 (Cb 0)) (hKmem 0 N)
      ((hKnorm 0 N).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _)))

end SubdiffusiveProcess.Paper
