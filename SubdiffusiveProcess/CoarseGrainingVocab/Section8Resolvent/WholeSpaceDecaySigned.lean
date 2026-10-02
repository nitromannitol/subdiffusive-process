import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecayLimit
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.MassiveWeakSolutionAlgebra




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped CompactlySupported ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-- Arbitrary signed compactly supported forcing for the divergence-form GMC
equation admits one global `L²` candidate, with local weak-solution
representatives on every centered cube. -/
theorem exists_localDivergenceMassiveWeakSolution_of_compactSupport_with_l2
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) :
    ∃ u : Vec d → ℝ,
      MemLp u 2 volume ∧
      (mu ^ 2 * ∫ x, u x ^ 2 ∂volume ≤ 4 * ∫ x, f x ^ 2 ∂volume) ∧
      ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
          IsMassiveWeakSolutionOn (coefficientAt M L omega) (fun _ ↦ 1)
            mu (cube d (k : ℤ)) uLocal f := by
  let fPlus : C_c(Vec d, ℝ) := f.nnrealPart.toReal
  let fMinus : C_c(Vec d, ℝ) := (-f).nnrealPart.toReal
  have hfPlus : ∀ x, 0 ≤ fPlus x := fun x ↦
    CompactlySupportedContinuousMap.toReal_nonneg x
  have hfMinus : ∀ x, 0 ≤ fMinus x := fun x ↦
    CompactlySupportedContinuousMap.toReal_nonneg x
  obtain ⟨_uCubePlus, _vPlus, uPlus, _hcontrolledPlus, _hvEqPlus,
      _hvMonoPlus, _hvBoundsPlus, _hvLimPlus, huPlusMem, huPlusEnergy,
      huPlusLocal⟩ :=
    exists_pointwiseMonotoneDivergenceMassiveCubeLimit_with_l2_and_local
      M L omega hmu fPlus hfPlus
  obtain ⟨_uCubeMinus, _vMinus, uMinus, _hcontrolledMinus, _hvEqMinus,
      _hvMonoMinus, _hvBoundsMinus, _hvLimMinus, huMinusMem, huMinusEnergy,
      huMinusLocal⟩ :=
    exists_pointwiseMonotoneDivergenceMassiveCubeLimit_with_l2_and_local
      M L omega hmu fMinus hfMinus
  have huMem : MemLp (uPlus - uMinus) 2 volume := huPlusMem.sub huMinusMem
  have hfMem : MemLp (fun x : Vec d ↦ f x) 2 volume :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have hfPlusMem : MemLp (fun x : Vec d ↦ fPlus x) 2 volume :=
    fPlus.continuous.memLp_of_hasCompactSupport fPlus.hasCompactSupport
  have hfMinusMem : MemLp (fun x : Vec d ↦ fMinus x) 2 volume :=
    fMinus.continuous.memLp_of_hasCompactSupport fMinus.hasCompactSupport
  have hpartSq : ∀ (g : C_c(Vec d, ℝ)) x, g.nnrealPart.toReal x ^ 2 ≤ g x ^ 2 := by
    intro g x
    simp only [CompactlySupportedContinuousMap.toReal_apply,
      CompactlySupportedContinuousMap.nnrealPart_apply, Real.coe_toNNReal']
    by_cases hx : 0 ≤ g x
    · rw [max_eq_left hx]
    · rw [max_eq_right (le_of_not_ge hx)]
      have hzero : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [hzero]
      exact sq_nonneg (g x)
  have hplusPoint : ∀ x, fPlus x ^ 2 ≤ f x ^ 2 := by
    intro x
    exact hpartSq f x
  have hminusPoint : ∀ x, fMinus x ^ 2 ≤ f x ^ 2 := by
    intro x
    calc
      fMinus x ^ 2 ≤ (-f) x ^ 2 := hpartSq (-f) x
      _ = f x ^ 2 := by
        change (-f x) ^ 2 = f x ^ 2
        ring
  have hplusIntegral : ∫ x, fPlus x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume :=
    integral_mono hfPlusMem.integrable_sq hfMem.integrable_sq hplusPoint
  have hminusIntegral : ∫ x, fMinus x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume :=
    integral_mono hfMinusMem.integrable_sq hfMem.integrable_sq hminusPoint
  have hdifference :
      ∫ x, (uPlus - uMinus) x ^ 2 ∂volume ≤
        2 * ∫ x, uPlus x ^ 2 ∂volume +
          2 * ∫ x, uMinus x ^ 2 ∂volume := by
    calc
      ∫ x, (uPlus - uMinus) x ^ 2 ∂volume ≤
          ∫ x, (2 * uPlus x ^ 2 + 2 * uMinus x ^ 2) ∂volume := by
        apply integral_mono huMem.integrable_sq
          ((huPlusMem.integrable_sq.const_mul 2).add
            (huMinusMem.integrable_sq.const_mul 2))
        intro x
        change (uPlus x - uMinus x) ^ 2 ≤
          2 * uPlus x ^ 2 + 2 * uMinus x ^ 2
        nlinarith [sq_nonneg (uPlus x + uMinus x)]
      _ = 2 * ∫ x, uPlus x ^ 2 ∂volume +
          2 * ∫ x, uMinus x ^ 2 ∂volume := by
        rw [integral_add, integral_const_mul, integral_const_mul]
        · exact huPlusMem.integrable_sq.const_mul 2
        · exact huMinusMem.integrable_sq.const_mul 2
  refine ⟨uPlus - uMinus, huMem, ?_, ?_⟩
  · calc
      mu ^ 2 * ∫ x, (uPlus - uMinus) x ^ 2 ∂volume ≤
          mu ^ 2 * (2 * ∫ x, uPlus x ^ 2 ∂volume +
            2 * ∫ x, uMinus x ^ 2 ∂volume) :=
        mul_le_mul_of_nonneg_left hdifference (sq_nonneg mu)
      _ = 2 * (mu ^ 2 * ∫ x, uPlus x ^ 2 ∂volume) +
          2 * (mu ^ 2 * ∫ x, uMinus x ^ 2 ∂volume) := by ring
      _ ≤ 2 * ∫ x, fPlus x ^ 2 ∂volume +
          2 * ∫ x, fMinus x ^ 2 ∂volume :=
        add_le_add (mul_le_mul_of_nonneg_left huPlusEnergy (by norm_num))
          (mul_le_mul_of_nonneg_left huMinusEnergy (by norm_num))
      _ ≤ 2 * ∫ x, f x ^ 2 ∂volume + 2 * ∫ x, f x ^ 2 ∂volume :=
        add_le_add (mul_le_mul_of_nonneg_left hplusIntegral (by norm_num))
          (mul_le_mul_of_nonneg_left hminusIntegral (by norm_num))
      _ = 4 * ∫ x, f x ^ 2 ∂volume := by ring
  · intro k
    obtain ⟨uPlusLocal, huPlusAE, huPlusSolution⟩ := huPlusLocal k
    obtain ⟨uMinusLocal, huMinusAE, huMinusSolution⟩ := huMinusLocal k
    refine ⟨uPlusLocal - uMinusLocal, ?_, ?_⟩
    · filter_upwards [huPlusAE, huMinusAE] with x hxPlus hxMinus
      simp only [H1Function.sub_toFun, Pi.sub_apply, hxPlus, hxMinus]
    · have hfPlusL2 : MemL2On (cube d (k : ℤ)) fPlus := hfPlusMem.restrict _
      have hfMinusL2 : MemL2On (cube d (k : ℤ)) fMinus := hfMinusMem.restrict _
      have hsolution := huPlusSolution.sub
        ((divergenceMassiveCubeBounds M L omega).ell k)
        ((divergenceMassiveCubeBounds M L omega).rho_measurable k)
        ((divergenceMassiveCubeBounds M L omega).rho_bounded k)
        hfPlusL2 hfMinusL2 huMinusSolution
      have hfDecomp : fPlus - fMinus = f := by
        simpa only [fPlus, fMinus] using
          (CompactlySupportedContinuousMap.nnrealPart_sub_nnrealPart_neg f)
      have hfDecompFun : (fPlus : Vec d → ℝ) - fMinus = f := by
        funext x
        exact congrArg (fun q : C_c(Vec d, ℝ) ↦ q x) hfDecomp
      simpa only [hfDecompFun] using hsolution

/-- Shift-normalized form of the signed compact-data construction.  It solves
`mu * u - div(a grad u) = mu * f`, so the global `L²` bound is independent of
`mu`.  Taking `mu = t⁻¹` is exactly the equation in the frozen whole-space
resolvent carrier and in source lines 11657--11669. -/
theorem exists_localDivergenceNormalizedMassiveWeakSolution_of_compactSupport_with_l2
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) :
    ∃ u : Vec d → ℝ,
      MemLp u 2 volume ∧
      (∫ x, u x ^ 2 ∂volume ≤ 4 * ∫ x, f x ^ 2 ∂volume) ∧
      ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
          IsMassiveWeakSolutionOn (coefficientAt M L omega) (fun _ ↦ 1)
            mu (cube d (k : ℤ)) uLocal (fun x ↦ mu * f x) := by
  obtain ⟨u, huMem, huEnergy, huLocal⟩ :=
    exists_localDivergenceMassiveWeakSolution_of_compactSupport_with_l2
      M L omega hmu (mu • f)
  have hforcingIntegral :
      ∫ x, (mu • f) x ^ 2 ∂volume = mu ^ 2 * ∫ x, f x ^ 2 ∂volume := by
    calc
      ∫ x, (mu • f) x ^ 2 ∂volume =
          ∫ x, mu ^ 2 * f x ^ 2 ∂volume := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by
          change (mu * f x) ^ 2 = mu ^ 2 * f x ^ 2
          ring
      _ = mu ^ 2 * ∫ x, f x ^ 2 ∂volume :=
        integral_const_mul (mu ^ 2) (fun x ↦ f x ^ 2)
  refine ⟨u, huMem, ?_, ?_⟩
  · apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hmu)).1
    calc
      mu ^ 2 * ∫ x, u x ^ 2 ∂volume ≤
          4 * ∫ x, (mu • f) x ^ 2 ∂volume := huEnergy
      _ = mu ^ 2 * (4 * ∫ x, f x ^ 2 ∂volume) := by
        rw [hforcingIntegral]
        ring
  · intro k
    obtain ⟨uLocal, huAE, huSolution⟩ := huLocal k
    refine ⟨uLocal, huAE, ?_⟩
    simpa only [Pi.smul_apply, smul_eq_mul] using huSolution

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
