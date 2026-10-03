module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.DirichletHessianWitness

@[expose] public section

/-!
# The canonical descendant Dirichlet budget at a free gap `N`

`exists_lintegral_oneStepDirichlet_descendantCellB_source_le` is stated for a
`choose`n Dirichlet solution, whereas the two-radius telescope needs the
*canonical* `oneStepOriginDirichletSolution` (its gradient is the one that
appears in `nfAxis_grad_split`).  The underlying estimate
`lintegral_descendantsAverage_oneStepCellB_four_le_of_cz_unit` takes the
solution family and the Calderon--Zygmund bound as inputs, so the canonical
witness of `exists_measurable_oneStepCanonicalDirichlet_cellB` can be fed to
it directly.

Instantiating the outer scale as `K = oneStepLocalizationScale n M.delta + N`
and the depth as `N` puts the *cells* at the localization scale — which is
what the `delta ^ 68` arithmetic requires — and leaves the gap `N` free, which
is what the two-radius harmonic limit requires.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- Canonical-solution descendant Dirichlet budget at gap `N`. -/
theorem exists_lintegral_nfOriginDirichlet_descendantCellB_source_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h N K : ℕ) (p : Vec d)
        (_hp : vecNormSq p = 1) (hh : 0 < h)
        (_hscale : (h : ℝ) ≤ M.delta⁻¹)
        (_hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
        (_hK : oneStepLocalizationScale n M.delta + N = K),
        ∃ (V : NFSample d → CubeVectorW1pFunction
              (originCube d (K : ℤ)) oneStepFourExponent)
          (hV : ∀ omega, (V omega).toField =
            (oneStepOriginDirichletSolution M n h p (K : ℤ) omega
              hh).toH1Function.grad),
          ∫⁻ omega, ENNReal.ofReal
              (descendantsAverage (originCube d (K : ℤ)) N (fun R =>
                if hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) N then
                  (oneStepCellB R
                    ((nfOriginDirichletHessianOf M n h p (K : ℤ) hh V hV
                      omega).restrict (isOpen_openCubeSet R)
                        (openCubeSet_subset_of_mem_descendantsAtDepth hR))) ^
                      (4 : ℕ)
                else 0)) ∂M.P.toMeasure ≤
            C * ENNReal.ofReal (M.delta ^ (68 : ℕ)) := by
  obtain ⟨Ccz, hCczTop, hcanon⟩ :=
    exists_measurable_oneStepCanonicalDirichlet_cellB d
  refine ⟨ENNReal.ofReal ((d : ℝ) ^ (8 : ℕ)) * Ccz ^ (4 : ℕ) *
    oneStepShellJacobianMatrixFourthConst d, ?_, ?_⟩
  · apply lt_top_iff_ne_top.2
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top hCczTop.ne))
      (by unfold oneStepShellJacobianMatrixFourthConst; finiteness)
  intro M n h N K p hp hh hscale hsource hK
  obtain ⟨V, hV, _hmeas, hbound⟩ := hcanon M n h p (K : ℤ) hh
  refine ⟨V, hV, ?_⟩
  have hmoment := lintegral_descendantsAverage_oneStepCellB_four_le_of_cz_unit
    (Q := originCube d (K : ℤ)) M n h N p hp hh hscale
    (fun omega =>
      (oneStepOriginDirichletSolution M n h p (K : ℤ) omega hh).toH1Function)
    (fun omega => nfOriginDirichletHessianOf M n h p (K : ℤ) hh V hV omega)
    (fun omega => by
      simpa only [nfOriginDirichletHessianOf,
        weakHessianOfCubeVectorW1pFour, oneStepFourExponent_exponent] using! (V omega).jacobianHilbertMemLp)
    Ccz hCczTop
    (fun omega => by
      simpa only [nfOriginDirichletHessianOf,
        weakHessianOfCubeVectorW1pFour] using hbound omega)
  refine hmoment.trans ?_
  have hKsub : K - oneStepLocalizationScale n M.delta = N := by omega
  have hKle : oneStepLocalizationScale n M.delta ≤ K := by omega
  set C : ℝ≥0∞ := ENNReal.ofReal ((d : ℝ) ^ (8 : ℕ)) * Ccz ^ (4 : ℕ) *
    oneStepShellJacobianMatrixFourthConst d with hC
  set ratio : ℝ := cubeScaleFactor (originCube d (K : ℤ)) /
    (3 : ℝ) ^ N / (3 : ℝ) ^ n with hratio
  have hratio0 : 0 ≤ ratio := by
    rw [hratio]
    exact div_nonneg (div_nonneg (cubeScaleFactor_nonneg _) (by positivity))
      (by positivity)
  have hsourceMoment :=
    ofReal_oneStep_source_ratio_four_mul_delta_four_le_delta_sixtyEight
      (d := d) M.shellPrefix.delta_pos
      (M.shellPrefix.delta_le_half.trans (by norm_num)) hsource hKle
  rw [hKsub] at hsourceMoment
  calc
    ENNReal.ofReal
          ((((cubeScaleFactor (originCube d (K : ℤ)) / (3 : ℝ) ^ N) /
                (3 : ℝ) ^ n) ^ (4 : ℕ)) * (d : ℝ) ^ (8 : ℕ)) *
        Ccz ^ (4 : ℕ) * oneStepShellJacobianMatrixFourthConst d *
          (ENNReal.ofReal M.delta) ^ (4 : ℝ) =
      C * (ENNReal.ofReal (ratio ^ (4 : ℕ)) *
        (ENNReal.ofReal M.delta) ^ (4 : ℝ)) := by
      rw [ENNReal.ofReal_mul (pow_nonneg hratio0 4)]
      dsimp only [C, ratio]
      ring
    _ ≤ C * ENNReal.ofReal (M.delta ^ (68 : ℕ)) := by
      gcongr

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
