import SubdiffusiveProcess.Paper.limiting_local_energy
import SubdiffusiveProcess.Sobolev.ResponseRecovery

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Topology SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal
noncomputable section
namespace Paper

/-- Finite limit-energy classes retain fractional coercivity along any convergent
coefficient sequence, including a selected cutoff subsequence. -/
theorem aux_mfd_prop_uniform_resolvent_fractional_limit
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube z r hr),
      ‖(v : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) v‖)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (K : ℝ) (hK : 0 < K)
    (hc : ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube z r hr)),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        K * sobolevCoefficientForm
          (a N)
          (v : SobolevData (centeredCube z r hr))
          (v : SobolevData (centeredCube z r hr)))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hsym : ∀ x y : DomainL2 (centeredCube z r hr),
      inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : DomainL2 (centeredCube z r hr), 0 ≤ inner ℝ x (G x))
    (hstrong : ∀ f : DomainL2 (centeredCube z r hr),
      Tendsto
        (fun N : ℕ =>
          (responseSolution (killedResponseSpace (Ω := centeredCube z r hr) hP)
            (a N) ((sobolevVolumeLoad f).comp
              (killedResponseSpace (Ω := centeredCube z r hr) hP).space.subtypeL)).val.1)
        atTop (𝓝 (G f))) :
    ∃ Cbase : ℝ, 0 < Cbase ∧
      ∀ u : DomainL2 (centeredCube z r hr),
        (limitFormEnergy G u).toENNReal ≠ ⊤ →
        ∃ v : CubeFractionalL2 (k := 1) hd z r hr threeQuarterOrder,
          v.val 0 = u ∧
          (cubeFractionalL2Norm hd z r hr threeQuarterOrder v) ^ 2 ≤
            Cbase * (limitFormEnergy G u).toReal := by
  obtain ⟨Cbase, hKC, hlimC⟩ := aux_limiting_local_energy_coercive_limit hd z r hr K hK
    (limitFormEnergy G) (limitFormEnergy_nonneg G)
    (fun u hu' => by
      obtain ⟨wseq, hwseq⟩ := exists_responseForm_recoverySequence
        (killedResponseSpace (Ω := centeredCube z r hr) hP) a G hsym hpos hstrong u hu'
      refine ⟨fun n => (wseq n).val.1,
        fun n => responseForm (killedResponseSpace (Ω := centeredCube z r hr) hP)
          (a n) (wseq n) (wseq n), hwseq.fst_nhds, hwseq.snd_nhds, ?_, ?_⟩
      · intro n
        exact Sf.h1_fractional_finite z r hr
          ⟨(wseq n).val, killedSobolevGraph_le_weakSobolevGraph (wseq n).property⟩
      · intro n
        simpa only [responseForm_apply, sobolevCoefficientForm_apply] using
          hc n ⟨(wseq n).val, (wseq n).property⟩)
    (fun w v hw => aux_limiting_local_energy_seminorm_le_liminf hd z r hr
      threeQuarterOrder w v hw)
  refine ⟨Cbase, lt_of_lt_of_le hK hKC, ?_⟩
  intro u hu
  have hfinite : limitFormEnergy G u < (⊤ : EReal) :=
    lt_top_iff_ne_top.mpr (EReal.toENNReal_ne_top_iff.mp hu)
  exact hlimC u hfinite.ne

end Paper
