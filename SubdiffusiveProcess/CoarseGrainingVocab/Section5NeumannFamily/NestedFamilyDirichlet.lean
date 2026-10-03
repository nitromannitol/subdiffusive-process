module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.NestedFamilyHarmonic

@[expose] public section

/-!
# The Dirichlet budget of the nested family

The nested family's Dirichlet member on the cell attached to `(S, R₀)` is,
by translation covariance of `oneStepCellB`, the origin-cube observable at
`R₀` evaluated at the translated sample.  Averaging over the overlap centres
is therefore stationarity, and averaging over `R₀ ∈ desc_k(P₀)` is a
*descendant* average — bounded by
`exists_lintegral_nfOriginDirichlet_descendantCellB_source_le` after paying
the `N`-independent constant `(3^d)^a`, `a` the fixed CZ interior depth.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- Gradient measurability of the canonical origin Dirichlet solution. -/
theorem measurable_nfOriginDirichlet_grad [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d) (m : ℤ)
    (hh : 0 < h) :
    Measurable fun omega : NFSample d =>
      H1Function.gradToHilbertVectorL2
        (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function := by
  apply measurable_oneStepShellDirichletGradL2 M n h p (originCube d m) hh
    (fun omega => oneStepOriginDirichletSolution M n h p m omega hh)
  intro omega phi
  have hweak :=
    oneStepOriginDirichletSolution_isWeakSolution M n h p m omega hh phi
  have hfield : ∀ x,
      (oneStepShellForcingH1 M n h omega p (originCube d m) hh).toField x =
        oneStepMultiplierAt M n h x omega • p := by
    intro x
    rw [oneStepShellForcing_paired_toField M n h omega p (originCube d m) hh,
      oneStepShellForcingW14_toField_apply]
  change (∫ x in openCubeSet (originCube d m),
      vecDot ((oneStepOriginDirichletSolution M n h p m omega hh
        ).toH1Function.grad x) (phi.toH1Function.grad x) ∂volume) = _
  calc
    _ = ∫ x in openCubeSet (originCube d m),
        vecDot (-oneStepMultiplierAt M n h x omega • p)
          (phi.toH1Function.grad x) ∂volume := by
      simpa only [matVecMul_identityCoeffField, one_mul] using hweak
    _ = -∫ x in openCubeSet (originCube d m),
        vecDot ((oneStepShellForcingH1 M n h omega p
          (originCube d m) hh).toField x)
          (phi.toH1Function.grad x) ∂volume := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      rw [hfield, neg_smul, vecDot_neg_left]

/-- The origin-cube descendant cell observable, extended by zero. -/
def nfOriginCellB [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d) (m : ℤ)
    (hh : 0 < h) (N : ℕ)
    (V : NFSample d → CubeVectorW1pFunction (originCube d m)
      oneStepFourExponent)
    (hV : ∀ omega, (V omega).toField =
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad)
    (R : TriadicCube d) (omega : NFSample d) : ℝ :=
  if hR : R ∈ descendantsAtDepth (originCube d m) N then
    oneStepCellB R
      ((nfOriginDirichletHessianOf M n h p m hh V hV omega).restrict
        (isOpen_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth hR))
  else 0

theorem nfOriginCellB_nonneg [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d) (m : ℤ)
    (hh : 0 < h) (N : ℕ) (V) (hV) (R : TriadicCube d)
    (omega : NFSample d) :
    0 ≤ nfOriginCellB M n h p m hh N V hV R omega := by
  unfold nfOriginCellB
  split_ifs with hR
  · unfold oneStepCellB
    exact mul_nonneg (cubeScaleFactor_nonneg _)
      (oneStepCellNormalizedHessianSize_nonneg _ _)
  · exact le_rfl

theorem measurable_nfOriginCellB [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d) (m : ℤ)
    (hh : 0 < h) (N : ℕ) (V) (hV) (R : TriadicCube d) :
    Measurable (nfOriginCellB M n h p m hh N V hV R) := by
  unfold nfOriginCellB
  split_ifs with hR
  · refine measurable_oneStepCellB R
      (fun omega =>
        (oneStepOriginDirichletSolution M n h p m omega hh
          ).toH1Function.restrict (isOpen_openCubeSet R)
            (openCubeSet_subset_of_mem_descendantsAtDepth hR))
      (fun omega =>
        (nfOriginDirichletHessianOf M n h p m hh V hV omega).restrict
          (isOpen_openCubeSet R)
          (openCubeSet_subset_of_mem_descendantsAtDepth hR)) ?_
    exact measurable_gradToHilbertVectorL2_of_grad_eq_restrict
      (openCubeSet_subset_of_mem_descendantsAtDepth hR)
      (fun omega =>
        (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function)
      _ (measurable_nfOriginDirichlet_grad M n h p m hh)
      (fun _omega => rfl)
  · exact measurable_const

/-- The fourth power of the origin cell observable is the budget's
integrand. -/
theorem nfOriginCellB_pow_four_eq [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d) (m : ℤ)
    (hh : 0 < h) (N : ℕ) (V) (hV) (R : TriadicCube d)
    (omega : NFSample d) :
    nfOriginCellB M n h p m hh N V hV R omega ^ (4 : ℕ) =
      (if hR : R ∈ descendantsAtDepth (originCube d m) N then
        (oneStepCellB R
          ((nfOriginDirichletHessianOf M n h p m hh V hV omega).restrict
            (isOpen_openCubeSet R)
            (openCubeSet_subset_of_mem_descendantsAtDepth hR))) ^ (4 : ℕ)
      else 0) := by
  unfold nfOriginCellB
  split_ifs with hR
  · rfl
  · norm_num

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
