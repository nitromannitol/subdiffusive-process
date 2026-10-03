module

public import SubdiffusiveProcess.Section10.ReversibleKilledSmoothing
public import SubdiffusiveProcess.Section10.KernelRowIntegralDomination

@[expose] public section

/-! A finite killed-row rectangle constant on each positive-side enclosing
cube, at each strictly positive time. The source Sobolev constants are
constructed from actual coefficient bounds. -/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

theorem exists_ae_killed_cube_row_bound {d : ℕ} (hd : 2 ≤ d)
    {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} [IsMarkovKernel law]
    (hD : LocalDiffusion c rho law) (z : Vec d) (L : ℝ) (hL : 0 < L)
    (t : NNReal) (ht : 0 < t) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ B : Set (Vec d), MeasurableSet B →
      ∀ᵐ x ∂((weightedMeasure rho).restrict (axisCube z L)),
        killedKernel law (axisCube z L) (isOpen_axisCube z L) t x B ≤
          ENNReal.ofReal A * ((weightedMeasure rho).restrict (axisCube z L)) B := by
  have hrc : ∀ W : Set (Vec d), IsCompact W → CoefficientOn W rho :=
    fun W hW ↦ (hD.2.1 W hW).2
  have hcc : ∀ W : Set (Vec d), IsCompact W → CoefficientOn W c :=
    fun W hW ↦ (hD.2.1 W hW).1
  have hm0 := (weightedMeasure_axisCube_pos hrc z L hL).ne'
  have hmtop := (weightedMeasure_axisCube_lt_top hrc z L).ne
  obtain ⟨p0, F, hp0, hF, hSob⟩ := exists_weighted_cube_sobolevAssumption hd z L hL c rho
    (coefficientOn_axisCube hcc z L) (coefficientOn_axisCube hrc z L)
    (weightedMeasure_axisCube_toReal_pos hrc z L hL)
  obtain ⟨_N, _hN, k, _hNk, hk⟩ := exists_iterate_eLpNorm_le p0 hp0
  let M : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ (k + 1) *
    ENNReal.ofReal (ultraConstant p0 * (1 : ℝ) ^ ((1 - 2 / p0)⁻¹) *
      (1 + F / ((t : ℝ) / ((k : ℝ) + 1))) ^ ((1 - 2 / p0)⁻¹)) *
        ((weightedMeasure rho) (axisCube z L))⁻¹)
  have hMtop : M ≠ ∞ := by
    dsimp only [M]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
        ENNReal.ofReal_ne_top) (ENNReal.inv_ne_top.mpr hm0)
  refine ⟨M.toReal, ENNReal.toReal_nonneg, fun B hB ↦ ?_⟩
  have htR : 0 < (t : ℝ) := NNReal.coe_pos.mpr ht
  have hbound := killedKernel_row_le hD (isOpenBoundedConvexDomain_axisCube z L)
    hm0 hmtop hp0 (le_refl 1) hF hSob k hk (t : ℝ) htR B hB
  simpa only [Real.toNNReal_coe, ENNReal.ofReal_toReal hMtop] using hbound

end SubdiffusiveProcess.Section10
