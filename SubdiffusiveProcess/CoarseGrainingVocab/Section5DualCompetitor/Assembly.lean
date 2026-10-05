module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.Final
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.RetainedCovered
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepDualGluedCellEnvelope

@[expose] public section




open MeasureTheory Homogenization Homogenization.Book Filter
open scoped BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure
open SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold
open SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Renormalized

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- The concrete dual-cell inputs in the dimensions where the reciprocal
one-step argument is used. -/
theorem dualCellMajorantInputs_of_three_le (d : ℕ) [NeZero d] (hd : 3 ≤ d) :
    DualCellMajorantInputs d := by
  classical
  let D : ℝ := (originCubeMeanZeroH1CoerciveEstimate d 0).constant
  obtain ⟨deltaO, O, hdeltaO, hO, hfold⟩ :=
    exists_oneStepDualOscillatory_shellEnlarged_sourceCells_budget d hd D
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
  refine ⟨deltaO, O, hdeltaO, hO, ?_⟩
  intro M hdelta n h q hq hh hblock hsource
  let ls : ℕ := oneStepLocalizationScale n M.delta
  let N₀ : ℕ := nfFoldRadius (nfAxisHarmonicDepth d hd) M.delta + 1
  let j₀ : ℕ → ℕ := fun K ↦ K - ls - N₀
  let covered : ℕ → Finset (TriadicCube d) := fun K ↦
    (oneStepSourceCells d K n M.delta).filter fun R ↦
      ∃ S ∈ overlapCentersAtDepth (originCube d (K : ℤ)) (j₀ K),
        R ∈ descendantsAtDepth S (N₀ - 1)
  let frac : ℕ → ℝ := uncoveredFractionBound d n M.delta (N₀ + 1)
  have hcovered : ∀ K, covered K ⊆ oneStepSourceCells d K n M.delta := by
    intro K R hR
    exact (Finset.mem_filter.mp hR).1
  have hfrac0 : Tendsto frac atTop (nhds 0) := by
    exact tendsto_uncoveredFractionBound_zero d n M.delta (N₀ + 1)
  have hfrac : ∀ K, ls + N₀ ≤ K →
      (((oneStepSourceCells d K n M.delta) \ covered K).card : ℝ) /
        ((oneStepSourceCells d K n M.delta).card : ℝ) ≤ frac K := by
    intro K hlarge
    have hK : oneStepLocalizationScale n M.delta ≤ K := by
      dsimp only [ls] at hlarge ⊢
      omega
    have hN : 1 ≤ N₀ := by
      dsimp only [N₀]
      omega
    have hjN : j₀ K + N₀ = K - oneStepLocalizationScale n M.delta := by
      dsimp only [j₀, ls] at hlarge ⊢
      omega
    apply card_sdiff_div_card_le_uncoveredFractionBound
      d n M.delta (N₀ + 1) covered K
    simpa only [covered] using
      (oneStepRetainedSourceCells_subset_overlapCentreCovered
        (d := d) hK hN hjN)
  have hsecond : DualGluedCellSecondMoment d :=
    dualGluedCellSecondMoment_of_pathwise d
      (exists_dualGluedCellPathwiseEnvelope d)
  obtain ⟨C, hmoment⟩ := hsecond M n h
  obtain ⟨boundaryBound, hboundary0, hboundary⟩ :=
    exists_dualPaperBoundaryLayer_expectation_bound M n h q hh
      (ls + N₀) covered hcovered frac hfrac0 hfrac C
      (fun K hlarge ↦ by
        have hK : oneStepLocalizationScale n M.delta ≤ K := by
          dsimp only [ls] at hlarge ⊢
          omega
        exact (hmoment K q hq hh hblock hsource hK).1)
      (fun K hlarge ↦ by
        have hK : oneStepLocalizationScale n M.delta ≤ K := by
          dsimp only [ls] at hlarge ⊢
          omega
        exact (hmoment K q hq hh hblock hsource hK).2.1)
      (fun K hlarge ↦ by
        have hK : oneStepLocalizationScale n M.delta ≤ K := by
          dsimp only [ls] at hlarge ⊢
          omega
        exact (hmoment K q hq hh hblock hsource hK).2.2)
  refine ⟨boundaryBound, hboundary0, eventually_atTop.2 ⟨ls + N₀, ?_⟩⟩
  intro K hlarge
  have hK : oneStepLocalizationScale n M.delta ≤ K := by
    dsimp only [ls] at hlarge ⊢
    omega
  obtain ⟨oscillatory, hoscInt, hosc0, hoscBudget, hfamily⟩ :=
    hfold M hdelta n h K q hq hh hblock hsource hK
  obtain ⟨j, N, F, hNdef, hjN, hgrad, _hcell, _hcoverage, hoscEq⟩ :=
    hfamily (by simpa only [ls, N₀] using hlarge)
  change N = N₀ at hNdef
  subst N
  have hj : j = j₀ K := by
    dsimp only [j₀, ls] at hjN ⊢
    omega
  subst j
  change oscillatory =
    oneStepDualOscillatoryMajorant M n h D
      (nfShellEnlargedCellB M n h K q hh
        (nfExtendByZero (nfNestedCell N₀) F.toCellFamily.neumann)) at hoscEq
  subst oscillatory
  let boundary : Sample d → ℝ := fun omega ↦
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
      ∑ R ∈ (oneStepSourceCells d K n M.delta) \ covered K,
        dualGluedCellHalfEnergyAt (K := K) M n h q hh R omega
  have hmomentK := hmoment K q hq hh hblock hsource hK
  have hboundaryInt : Integrable boundary M.P.toMeasure := by
    dsimp only [boundary]
    exact (integrable_finsetSum
      ((oneStepSourceCells d K n M.delta) \ covered K)
      (fun R hR ↦ hmomentK.1 R (Finset.mem_sdiff.mp hR).1)).const_mul _
  have hboundaryMean :
      ∫ omega, boundary omega ∂M.P.toMeasure ≤ boundaryBound K := by
    simpa only [boundary, dualGluedCellHalfEnergyAt] using
      hboundary K hlarge
  have hfactorAE : ∀ᵐ omega ∂M.P.toMeasure,
      ∀ R ∈ oneStepSourceCells d K n M.delta,
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareLowerEllipticityFactor R
            (aCutoffEnvelopeTriadicCoeffFamily M (n + h) omega)
              (1 / 4 : ℝ) (.finite 1)) ^ 2 =
          oneStepLowerPoincareEnergyFactorMeasurable M (n + h)
            (oneStepLocalizationScale n M.delta)
            (translatePotentialSequence (triadicCubeShift R) omega) := by
    exact (Finset.eventually_all
      (oneStepSourceCells d K n M.delta)).2 fun R hR ↦
        oneStepLowerPoincareFactor_cell_ae_eq_measurable_translate
          M (n + h) R (oneStepSourceCells_scale_eq hK hR)
  refine ⟨
    oneStepDualOscillatoryMajorant M n h D
      (nfShellEnlargedCellB M n h K q hh
        (nfExtendByZero (nfNestedCell N₀) F.toCellFamily.neumann)),
    boundary, hboundaryInt, hboundaryMean, hoscInt, hosc0, ?_, hoscBudget⟩
  filter_upwards [hfactorAE] with omega hfactor
  have hcompetitor :=
    half_randomAStarInv_le_normalized_paperMajorantSum_of_covered
      (j := K - oneStepLocalizationScale n M.delta)
      M n h q omega hh
      (dualParentEllipticityData M (n + h) omega
        (originCube d (K : ℤ))).isElliptic
      (dualParentEllipticityData_descendants M (n + h) omega
        (originCube d (K : ℤ))
        (K - oneStepLocalizationScale n M.delta))
      (covered K)
      (fun R ↦ oneStepDualPrincipalMajorant (K := K) M n h q R omega hh)
      (fun R ↦ oneStepDualOscillatoryMajorant M n h D
        (nfShellEnlargedCellB M n h K q hh
          (nfExtendByZero (nfNestedCell N₀) F.toCellFamily.neumann)) R omega)
      (fun R ↦ oneStepDualPrincipalMajorant_nonneg M n h q R omega hh)
      (by
        intro R
        have hbase : 0 ≤ nfExtendByZero (nfNestedCell N₀)
            F.toCellFamily.neumann R omega :=
          nfExtendByZero_nonneg
            (fun i omega ↦ F.toCellFamily.neumann_nonneg i
              (Finset.mem_univ i) omega) R omega
        have hB : 0 ≤ nfShellEnlargedCellB M n h K q hh
            (nfExtendByZero (nfNestedCell N₀) F.toCellFamily.neumann) R omega := by
          exact mul_nonneg (Nat.cast_nonneg d)
            (add_nonneg (oneStepShellForcingCellB_nonneg M n h omega q hh)
              hbase)
        have hfactor0 : 0 ≤ oneStepLowerPoincareEnergyFactorMeasurable
            M (n + h) (oneStepLocalizationScale n M.delta)
              (translatePotentialSequence (triadicCubeShift R) omega) := by
          unfold oneStepLowerPoincareEnergyFactorMeasurable
          exact mul_nonneg
            (mul_nonneg (sq_nonneg _)
              (inv_nonneg.mpr (ahom_pos M (n + h)).le))
            (le_max_right _ _)
        exact mul_nonneg
          (mul_nonneg (oneStepDualCellEnergyConst_nonneg d) hfactor0)
          (oneStepCellBesovError_nonneg
            (mul_nonneg
              (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg hB)
            hB))
      (fun R hR ↦
        volumeAverage_paperPrincipalCell_energy_le_majorant
          M n h q R omega hh
          (dualParentEllipticityData_descendants M n omega
            (originCube d (K : ℤ))
            (K - oneStepLocalizationScale n M.delta))
          (dualParentEllipticityData_descendants M (n + h) omega
            (originCube d (K : ℤ))
            (K - oneStepLocalizationScale n M.delta)) hR)
      (by
        intro R hRcovered hRdesc
        have hRsource : R ∈ oneStepSourceCells d K n M.delta :=
          hcovered K hRcovered
        obtain ⟨_hRsource', S, hS, hRS⟩ := Finset.mem_filter.mp hRcovered
        obtain ⟨i, hi, hBext⟩ :=
          exists_nfExtendByZero_innerHalf_eq hS hRS F.toCellFamily.neumann
        obtain ⟨uFam, HFam, hgradFam, hBFam⟩ :=
          exists_cellHessian_of_cell_eq F hi omega
        have hRQ : openCubeSet R ⊆
            openCubeSet (originCube d (K : ℤ)) :=
          openCubeSet_subset_of_mem_descendantsAtDepth hRdesc
        let uTri : H1Function (openCubeSet R) :=
          (oneStepTriadicNeumannSolution M n h q
            (originCube d (K : ℤ)) omega hh).toH1Function.restrict
              (isOpen_openCubeSet R) hRQ
        have haeQ :=
          oneStepTriadicNeumannSolution_grad_ae_eq_originSolution
            M n h q (K : ℤ) omega hh
        have haeR := haeQ.filter_mono
          (ae_mono (Measure.restrict_mono_set volume hRQ))
        have htriFam :
            uTri.grad =ᵐ[volumeMeasureOn (openCubeSet R)] uFam.grad := by
          filter_upwards [haeR] with x hx
          change
            (oneStepTriadicNeumannSolution M n h q
              (originCube d (K : ℤ)) omega hh).toH1Function.grad x =
              uFam.grad x
          rw [hgradFam, hgrad i omega]
          exact hx
        let HTri : HasWeakHessianOn (openCubeSet R) uTri :=
          weakHessianOfGradAeEq htriFam HFam
        have hB :
            oneStepCellB R HTri ≤
              nfExtendByZero (nfNestedCell N₀)
                F.toCellFamily.neumann R omega := by
          calc
            oneStepCellB R HTri = oneStepCellB R HFam := rfl
            _ = F.toCellFamily.neumann i omega := hBFam
            _ ≤ nfExtendByZero (nfNestedCell N₀)
                F.toCellFamily.neumann R omega := (hBext omega).symm.le
        have hraw :=
          dualPaperRawOscillatory_le_dualOscillatoryMajorant_onCell
            M n h q omega hh R hRsource uTri HTri rfl
            (nfExtendByZero (nfNestedCell N₀) F.toCellFamily.neumann)
            hB (hfactor R hRsource)
        simpa only [dualPaperRawOscillatory, dite_eq_left hRsource] using hraw)
  simpa only [boundary, dualGluedCellHalfEnergyAt, oneStepSourceCells] using
    hcompetitor

/-- The high-dimensional wrapper expected by the sharp-asymptotic closure. -/
theorem dualCellMajorantInputsOfNeZero (d : ℕ) :
    DualCellMajorantInputsOfNeZero d := by
  intro hd
  let : NeZero d := ⟨by omega⟩
  exact dualCellMajorantInputs_of_three_le d hd

/-- Final source-facing sharp asymptotic. -/
theorem sharp_asymptotic_final {d : ℕ} :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        M.delta ≤ delta0 → ∀ m : ℕ,
          |Real.log (ahom M m) +
              2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
            C * M.delta ^ 2 * |Real.log M.delta| *
              (1 + (m : ℝ) * M.delta) :=
  sharp_asymptotic_of_concrete (dualCellMajorantInputsOfNeZero d)

/-- Final source-facing renormalized-diffusivities theorem. -/
theorem renormalized_diffusivities_final {d : ℕ} :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        ∃ eta : ℝ, 0 < eta ∧
          (∀ n m : ℕ, n ≤ m →
            Real.exp (-(m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) ≤
                ahom M m ∧
            ahom M m ≤ ahom M n ∧
            ahom M n ≤ min 1
              (Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P *
                ((m - n : ℕ) : ℝ)) * ahom M m) ∧
            ahom M m ≤ Real.rpow 3 (-eta * (m + 1 : ℝ))) ∧
          (d = 2 → ∀ m : ℕ,
            ahom M m =
              Real.exp (-(m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) ∧
          (M.delta ≤ delta0 → ∀ m : ℕ,
            |Real.log (ahom M m) +
                2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
              C * M.delta ^ 2 * |Real.log M.delta| *
                (1 + (m : ℝ) * M.delta)) :=
  renormalized_diffusivities_of_sharp_asymptotic sharp_asymptotic_final

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
