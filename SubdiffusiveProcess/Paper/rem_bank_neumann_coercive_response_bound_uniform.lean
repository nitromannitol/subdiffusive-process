import SubdiffusiveProcess.Paper.rem_bank_neumann_coercive_uniform

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Real-algebra choice of a coercive-block order pair `(p', q')` valid for ANY `p ≥ 1`:
`p' := max 2 p`, `q' := p' + 1` satisfies `2 ≤ p'`, `p' < q'`, `4p ≤ 12p'` and `4p ≤ 4q'` --
the two inequalities needed to downgrade `rem_bank_neumann_coercive_uniform`'s order-`12p'`/`4q'`
bound to order `4p` via Lyapunov monotonicity. -/
theorem aux_rem_bank_neumann_coercive_response_bound_uniform_order_choice (p : ℝ) (hp : 1 ≤ p) :
    2 ≤ max 2 p ∧ max 2 p < max 2 p + 1 ∧
      4 * p ≤ 12 * max 2 p ∧ 4 * p ≤ 4 * (max 2 p + 1) := by
  refine ⟨le_max_left _ _, by linarith, ?_, ?_⟩
  · rcases le_or_gt p 2 with h | h
    · have hm : max 2 p = 2 := max_eq_left h
      rw [hm]; linarith
    · have hm : max 2 p = p := max_eq_right h.le
      rw [hm]; linarith
  · have hle : p ≤ max 2 p := le_max_right _ _
    linarith



theorem rem_bank_neumann_coercive_response_bound_uniform (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : Paper.in_J d) (P : Paper.in_poincare d hd E)
    (Sfi : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd) (p : ℝ) (hp : 1 ≤ p)
    (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho) (hrho0 : ∀ v : ℝ, 0 ≤ rho v)
    (hrhos : ∀ v : ℝ, v ∉ Set.Ioo (1 : ℝ) 2 → rho v = 0) (hrhoi : (∫ v, rho v) = 1)
    (pvec : Fin d → ℝ) (hpvec : (∑ i : Fin d, (pvec i) ^ 2) = 1)
    (hPn : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(w : SobolevData (unitNeumannCube d)).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w‖) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ min 1 delta0 →
        let Pm0 : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
        let Sn : ResponseSpace (unitNeumannCube d) := meanZeroResponseSpace hPn
        let an : ℕ → BilateralField d → PositiveCoefficient (unitNeumannCube d) := fun N omega =>
            cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
        let Lp : Sn.space →L[ℝ] ℝ :=
            (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))
        let yn : ℕ → BilateralField d → ℝ := fun N omega => inverseResponse Sn (an N omega) Lp
        ∃ Kcoerc : ℕ → BilateralField d → ℝ,
          (∀ N, ∀ omega, 0 ≤ Kcoerc N omega ∧
            (∀ v : meanZeroSobolevGraph (unitNeumannCube d),
                cubeFractionalSqNorm hd (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
                    v.val.1 ≤
                  Kcoerc N omega * sobolevCoefficientForm (an N omega) v.val v.val)) ∧
          (∀ N, MemLp (Kcoerc N) (ENNReal.ofReal (4 * p)) Pm0 ∧
                MemLp (yn N) (ENNReal.ofReal (4 * p)) Pm0) ∧
          (∀ N, eLpNorm (Kcoerc N) (ENNReal.ofReal (4 * p)) Pm0 ≤ ENNReal.ofReal B ∧
                eLpNorm (yn N) (ENNReal.ofReal (4 * p)) Pm0 ≤ ENNReal.ofReal B) := by
  obtain ⟨h2p', hp'q', h4p12, h4p4q⟩ :=
    aux_rem_bank_neumann_coercive_response_bound_uniform_order_choice p hp
  obtain ⟨delta0, hdelta0, B9, Bsm, hB90, hBsm0, hmain⟩ :=
    rem_bank_neumann_coercive_uniform d hd E P Sfi (max 2 p) (max 2 p + 1) h2p' hp'q'
      rho hrho hrho0 hrhos hrhoi pvec hpvec hPn
  refine ⟨delta0, hdelta0, B9, hB90, fun M Rm H hIC hδ => ?_⟩
  obtain ⟨Kcoerc, hKcoerc, hKmem, hKnorm, -⟩ := hmain M Rm H hIC hδ
  refine ⟨Kcoerc, hKcoerc, fun N => ⟨?_, ?_⟩, fun N => ⟨?_, ?_⟩⟩
  · exact (hKmem N).1.mono_exponent (ENNReal.ofReal_le_ofReal h4p12)
  · exact (hKmem N).2.2.2.mono_exponent (ENNReal.ofReal_le_ofReal h4p4q)
  · refine (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal h4p12)
      (hKmem N).1.aestronglyMeasurable).trans ?_
    exact (le_self_add.trans (le_self_add.trans le_self_add)).trans (hKnorm N)
  · refine (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal h4p4q)
      (hKmem N).2.2.2.aestronglyMeasurable).trans ?_
    exact le_add_self.trans (hKnorm N)

end Paper
