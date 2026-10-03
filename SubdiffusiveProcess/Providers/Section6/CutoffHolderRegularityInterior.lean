module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.CutoffGammaOneTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.UncutGammaOneTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.CampanatoFull
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.CampanatoFullGate
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneArithmetic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneCarriers
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneInstantiation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.DescentPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowThreeShort
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoCoverApplied
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.OscillationLegCompose
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.StoppingRowsRaised
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoOscLeg
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.ScalarEnergyIdentity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyRow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyRowScalar
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.ExcessDecayAdapter
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.StoppingSplit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoAtStep
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.GammaOneComposition
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.StepSeven
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.DimensionZero
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.OuterAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.PackageAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.TailSaturation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffAnchor
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffComparisonCollapse
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffExcessDecay
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecayInterior.InteriorHarmonic
public import SubdiffusiveProcess.Frozen.Section6.HarmonicApproximationGoodScalesInterior
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.CutoffHolderScale

@[expose] public section




namespace SubdiffusiveProcess.Providers.Section6

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Provider-local name for the sole provisional conclusion consumed by the
interior Hölder ladder. -/
abbrev InteriorHolderExcessDecayInput (d : ℕ) : Prop :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.InteriorHolderExcessDecayInput d

/-- The geometric content of the frozen `cube d (m-1)` binder: an interior base
point never produces a boundary-touching window at the scales the ladder uses. -/
theorem interiorHolderRegularity_gate {d : ℕ} {m n : ℤ} {x : Vec d}
    (hx : x ∈ cube d (m - 1)) (hn : n ≤ m - 5) :
    ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) :=
  not_boundaryTouches_of_interior hx hn

/-- The frozen interior three-row conclusion has no exceptional
zero-dimensional case. -/
theorem interiorHolderRegularityConclusions_dim_zero
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel 0) (C : ℝ) (hC : 0 ≤ C)
    (L : ℕ) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample 0) (alpha : ℝ)
    (m X : ℕ) (u : H1Function (openCubeSet (originCube 0 m)))
    (g : Vec 0 → Vec 0) :
    InteriorHolderRegularityConclusions M C L ω alpha m X u g := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.interiorHolderRegularityConclusions_dim_zero (M := M) (C := C) (hC := hC) (L := L) (ω := ω) (alpha := alpha) (m := m) (X := X) (u := u) (g := g)



theorem exists_cutoffHolderRegularityInterior_of_pathwiseInputs
    (d : ℕ) (C : ℝ) (hC : 0 < C)
    (hpath : InteriorCutoffPathwiseInput d C)
    (huniform : InteriorCutoffUniformInput d C) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      (M.delta ≤ C⁻¹ →
      ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
        ∀ L m : ℕ,
          (∃ X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
            Measurable X ∧ (∀ ω, 0 < X ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ ω, ∀ (u : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d),
              IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
                  (cube d m) u g →
              MemHolder (cube d m) (1 / 2) g →
              InteriorHolderRegularityConclusions M C L ω alpha m (X ω) u g) ∧
          (m ≤ L → ∃ Xuncut : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
            Measurable Xuncut ∧ (∀ ω, 0 < Xuncut ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xuncut ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ J : ℕ, m ≤ J → ∀ ω,
              ∀ (u : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M J ω)
                    (cube d m) u g →
                MemHolder (cube d m) (1 / 2) g →
                InteriorHolderRegularityConclusions M C J ω alpha m (Xuncut ω) u g) ∧
          ∀ y : Vec d,
            (∃ Xy : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
              Measurable Xy ∧ (∀ ω, 0 < Xy ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xy ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ ω, ∀ (u : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDivFormWeakSolutionOn
                    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
                      (translatePotentialSample y ω))
                    (cube d m) u g →
                MemHolder (cube d m) (1 / 2) g →
                InteriorHolderRegularityConclusions M C L (translatePotentialSample y ω)
                  alpha m (Xy ω) u g) ∧
            (m ≤ L → ∃ XuncutY : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
              Measurable XuncutY ∧ (∀ ω, 0 < XuncutY ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < XuncutY ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ J : ℕ, m ≤ J → ∀ ω,
                ∀ (u : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d),
                  IsDivFormWeakSolutionOn
                      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M J
                        (translatePotentialSample y ω))
                      (cube d m) u g →
                  MemHolder (cube d m) (1 / 2) g →
                  InteriorHolderRegularityConclusions M C J (translatePotentialSample y ω)
                    alpha m (XuncutY ω) u g)) :=
  exists_cutoffHolderRegularityInterior_of_inputs d C hC hpath huniform

/-- Steps 3--5 of the printed ladder on the interior branch, on the exact
interior draft input: the concrete recurrence families, interval sums,
bad-scale set and the proved iteration lemma composed into the full-domain
Campanato estimate before the final `C₁` absorption.  No datum norm survives in
the defect budget. -/
noncomputable def interiorHolderRegularity_campanatoFull {d : ℕ} [NeZero d]
    (hExcess : InteriorHolderExcessDecayInput d) :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorHolderCampanatoFull
    d hExcess

/-- Step 7 on the interior branch: the arbitrary-centre excess row.  Its
conclusion is byte-for-byte the third row of the frozen interior package. -/
noncomputable def interiorHolderRegularity_stepSeven (d : ℕ) :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.interiorStepSeven_of_short_and_scaledGrid d

/-- The finite-cutoff stopping package at the manuscript's Hölder parameters.
This is the datum-free carrier of the frozen `X`: measurable, positive, and
beyond it both pathwise controls hold at every admissible grid centre.  Only
its `Γ₁` tail estimate is missing, and that is what
`InteriorCutoffPathwiseInput` / `InteriorCutoffUniformInput` still carry. -/
theorem interiorCutoffHolderRegularity_measurable_stopping_controls {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (C1 C2 alpha : ℝ)
    (step m : ℕ) :
    let X := Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
      (Section6Stopping.holderStoppingLambda C1 alpha)
      (Section6Stopping.holderStoppingEpsilon C2 alpha) step m
    Measurable X ∧ (∀ omega, 0 < X omega) ∧
      ∀ omega, ∀ n : ℕ, (X omega : ℤ) ≤ (m : ℤ) - (n : ℤ) →
        ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d m →
          (∑ j ∈ Finset.Icc n m,
              accumulatedError M (some L) j z
                Section6Stopping.holderStoppingS omega) ≤
              Section6Stopping.holderStoppingLambda C1 alpha *
                ((m : ℝ) - (n : ℝ)) ∧
            (∑ j ∈ Finset.Icc n m,
                (1 - if omega ∈ goodEvent M (some L) j z
                  (Section6Stopping.holderStoppingEpsilon C2 alpha)
                  Section6Stopping.holderStoppingS then 1 else 0)) <
              1 + Section6Stopping.holderStoppingLambda C1 alpha *
                ((m : ℝ) - (n : ℝ)) := by
  dsimp only
  refine ⟨Section6Stopping.measurable_measurableCutoffHolderStoppingScale
    M L alpha (Section6Stopping.holderStoppingLambda C1 alpha)
      (Section6Stopping.holderStoppingEpsilon C2 alpha) step m,
    fun omega => Section6Stopping.measurableCutoffHolderStoppingScale_pos
      M L alpha (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega, ?_⟩
  intro omega n hn z hzgrid hzmem
  exact Section6Stopping.measurableCutoffHolder_stopped_controls_at_parameters
    M L C1 C2 alpha step m n omega hn z hzgrid hzmem

/-! ### Step 6 on the interior branch -/



abbrev InteriorCellEnergyInput (d : ℕ) : Prop :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.InteriorCellEnergyInput d



theorem interiorHolderRegularity_no_boundary_cell {d : ℕ} {m n top : ℤ}
    {z x q : Vec d} (hz : z ∈ cube d (m - 1)) (hx : x ∈ truncatedCube d m n z)
    (hntop : n ≤ top) (htop : top ≤ m - 5)
    (hq : q ∈ truncatedCube d m (top - 1) x) :
    openCubeAtScale q (top - 3) ⊆ cube d m :=
  openCubeAtScale_subset_cube_of_interior_descendant hz hx hntop htop hq



noncomputable def interiorHolderRegularity_projectedEnergy {d : ℕ} [NeZero d]
    (hcell : InteriorCellEnergyInput d) :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorHolderProjectedEnergy
    d hcell



theorem interiorCellEnergyInput_of_harmonicLane (d : ℕ) [NeZero d] :
    InteriorCellEnergyInput d :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.interiorCellEnergyInput_of_harmonicLane d

/-- **Interior Step 6 carries no premise at all.**  This is where the interior
anchor overtakes the boundary one, whose Step 6 still owes the affine-covariant
active-cell remainder for boundary cells — a branch the interior re-cut does not
have. -/
noncomputable def interiorHolderRegularity_projectedEnergyFinal (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorHolderProjectedEnergy_final d

/-! ### Adapters and the separated obligations -/



theorem interiorHolderExcessDecayInput_of_containmentForm {d : ℕ}
    (h : InteriorHolderExcessDecayContainmentForm d) :
    InteriorHolderExcessDecayInput d :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.interiorHolderExcessDecayInput_of_containmentForm h

/-- The fixed-cutoff package, with its witness pinned to the landed carrier and
probability separated from analysis. -/
theorem interiorCutoffPathwiseInput_of_parts {d : ℕ} {C : ℝ} {step : ℕ}
    (htail : CutoffStoppingGammaOneTail d C step)
    (hrows : InteriorCutoffDeterministicRows d C step) :
    InteriorCutoffPathwiseInput d C := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.interiorCutoffPathwiseInput_of_parts (d := d) (C := C) (step := step) (htail := htail) (hrows := hrows)

/-- The cutoff-uniform package, with its witness pinned to the
cutoff-independent carrier — the machine form of the H7 "may take equal"
reading. -/
theorem interiorCutoffUniformInput_of_parts {d : ℕ} {C : ℝ} {step : ℕ}
    (htail : UncutStoppingGammaOneTail d C step)
    (hrows : InteriorUncutDeterministicRows d C step) :
    InteriorCutoffUniformInput d C := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.interiorCutoffUniformInput_of_parts (d := d) (C := C) (step := step) (htail := htail) (hrows := hrows)

/-! ### The Γ₁ tails are theorems -/

/-- **The finite-cutoff Γ₁ tail is proved.**  The combined stopping scale at the
manuscript's Hölder parameters satisfies the frozen Γ₁ bound. -/
theorem exists_cutoffGammaOneTail (d : ℕ) [NeZero d] (step : ℕ) {C1 C2 : ℝ}
    (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) :
    ∃ C : ℝ, 0 < C ∧ CutoffGammaOneTailAt d C C1 C2 step := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_cutoffGammaOneTail (d := d) (step := step) (C1 := C1) (C2 := C2) (hC1 := hC1) (hC2 := hC2)

/-- **The cutoff-independent Γ₁ tail is proved.**  Its carrier does not mention
the cutoff, which is what lets one witness serve every `J ≥ m` (D-011/H7). -/
theorem exists_uncutGammaOneTail (d : ℕ) [NeZero d] (step : ℕ) {C1 C2 : ℝ}
    (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) :
    ∃ C : ℝ, 0 < C ∧ UncutGammaOneTailAt d C C1 C2 step := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_uncutGammaOneTail (d := d) (step := step) (C1 := C1) (C2 := C2) (hC1 := hC1) (hC2 := hC2)

/-- **The frozen interior anchor from the deterministic rows alone.**  Every
probabilistic obligation of the interior anchor is discharged. -/
noncomputable def interiorCutoffHolderRegularity_ofRows (d : ℕ) [NeZero d] :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_cutoffHolderRegularityInterior_of_rows d

/-! ### S3: the row-1 passage -/

/-- The interior gate at every admissible scale around a descendant centre.
This is the form frozen row 1 needs: its grid centres are descendants of the
frozen base point, not points of `cube d (m-1)`. -/
theorem interiorHolderRegularity_gate_descendant {d : ℕ} {m n : ℤ} {x y : Vec d}
    (hx : x ∈ cube d (m - 1)) (hy : y ∈ truncatedCube d m n x) (hn : n ≤ m - 5)
    {j : ℤ} (hj : j ≤ m - 5) :
    ¬ BoundaryTouches (truncatedCube d m j y) (cube d m) :=
  interiorGate_of_descendant hx hy hn hj

/-- Steps 3--5 with the interior gate carried as a hypothesis, the form the
row-1 passage consumes. -/
noncomputable def interiorHolderRegularity_campanatoFullGate {d : ℕ} [NeZero d]
    (hExcess : InteriorHolderExcessDecayInput d) :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorHolderCampanatoFullGate
    d hExcess



noncomputable def interiorHolderRegularity_rowOneArith (d : ℕ) :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.interiorRowOne_arith d

/-- **Frozen row 1 at every base scale**, from the deep-range Campanato output
and the shallow-range top-window transfer.  Row 1 is complete as arithmetic;
what remains is instantiating the Campanato output at the manuscript's
parameters. -/
noncomputable def interiorHolderRegularity_rowOneCombined (d : ℕ) :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.interiorRowOne_combined d

/-- The ladder's coefficient carrier is the frozen row's tail average.  Without
this identity the ladder's `topForcing` and the frozen data slot are different
expressions and no row assembles. -/
theorem interiorHolderRegularity_tailCarrier {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    tailCoefficientCubeAverage M L m ω = tailAverage M L m ω (cube d (m : ℤ)) :=
  tailCoefficientCubeAverage_eq_tailAverage_cube M L m ω

/-! ### Row 1 with a gap-uniform constant, and the parameter instantiation -/

/-- **Frozen row 1 at every base scale, with a gap-uniform constant.**  The
coefficient-ratio factor of the ladder grows with the gap, so it must be
absorbed jointly with the ladder exponential; this is the form that actually
feeds row 1. -/
noncomputable def interiorHolderRegularity_rowOneJoint (d : ℕ) :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.interiorRowOne_combinedJoint d

/-- The two stopped controls at a grid centre and at the origin — the pair
`stopped_tailAverage_ratio_bounds_exp` needs. -/
noncomputable def interiorHolderRegularity_stoppedControls (d : ℕ) :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.stoppedControls_pair d

/-- The coefficient-ratio row of the gated Campanato estimate, at the stopping
scale, with the gap-uniform exponential bound. -/
noncomputable def interiorHolderRegularity_ratioRow (d : ℕ) :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.stoppedRatio_row d

/-- The gated Campanato output at top depth `top + 5 = m` is literally the
`hlong` hypothesis of the row-1 assembly: integer scale exponents become real
ones, the top depth becomes `m - 5`, and the ladder's coefficient carrier
becomes the frozen one.  With this in place the remaining instantiation is a
pure supply of hypotheses, with no rewriting left. -/
noncomputable def interiorHolderRegularity_shapeMatch (d : ℕ) :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.campanatoOutput_to_hlong d

/-! ### The row-1 instantiation inputs -/

/-- **The stopping scale never drops below `5`**, so the frozen hypothesis
`X ≤ m - n` already places the base point five scales inside the domain — which
is exactly what the interior gate needs at the frozen row's base points. -/
theorem interiorHolderRegularity_baseScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m n : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hstop : (Section6Stopping.measurableHolderStoppingScale M alpha lambda
        epsilon step m omega : ℤ) ≤ (m : ℤ) - (n : ℤ)) :
    (n : ℤ) ≤ (m : ℤ) - 5 :=
  base_scale_le_of_stopping M alpha lambda epsilon step m n omega hstop

/-- The joint absorption of the ladder exponential and the coefficient ratio —
the step that makes the row-1 constant gap-uniform. -/
noncomputable def interiorHolderRegularity_jointAbsorption :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.expAbar_mul_ratio_le

/-- The top window at depth `m - 5` against the global oscillation. -/
noncomputable def interiorHolderRegularity_topWindow (d : ℕ) :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.topWindow_le_global d

/-- The shallow window at depth `ell`, valid exactly when `m - ell ≤ 5`. -/
noncomputable def interiorHolderRegularity_shallowWindow (d : ℕ) :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.shallowWindow_le_global d

/-! ### Frozen row 1 -/

/-- **Frozen row 1 for the interior anchor is closed**, conditional only on
`InteriorHolderExcessDecayInput`.  The gated Campanato estimate is instantiated
at the manuscript's parameters and at the maximal admissible top depth `m - 5`,
the ladder exponential and the coefficient ratio are absorbed jointly (so the
constant is gap-uniform), and the shallow range is covered by the top-window
transfer alone. -/
noncomputable def interiorHolderRegularity_rowOne (d : ℕ) [NeZero d] :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorRowOne d

/-- The deep-branch Campanato output at the manuscript's parameters — the
~20-argument application, with the joint absorption bound attached. -/
noncomputable def interiorHolderRegularity_campanatoOutput (d : ℕ) [NeZero d] :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorCampanatoOutput d

/-! ### Frozen row 2: the conversion -/

/-- **The row-2 conversion.**  Interior Step 6 is unconditional and its
square-root budget splits by the scalar core; once each of the two legs is
bounded by the frozen gap factor, the frozen row-2 shape follows under a single
constant.

The oscillation leg is *not* dischargeable from row 1 as it stands: row 1
controls the oscillation only at grid points (`OnTriadicGrid ell y`), while
frozen row 2's base point `x ∈ cube d (m-1)` carries no grid binder.  Row 2
therefore needs an off-grid transfer of the oscillation, exactly as Step 7 needs
one for the excess.  Keeping the leg explicit makes that requirement visible. -/
noncomputable def interiorHolderRegularity_rowTwoConversion (d : ℕ) :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.interiorRowTwo_of_budget d

/-! ### The off-grid oscillation transfer -/



theorem interiorHolderRegularity_offGridOscillation {d : ℕ} {m j ell : ℤ}
    {x z : Vec d} (hx : x ∈ cube d m) (hz : z ∈ cube d m)
    (hjm : j - 1 ≤ m) (hellm : ell - 1 ≤ m)
    (hsub : truncatedCube d m j x ⊆ truncatedCube d m ell z)
    (u : H1Function (openCubeSet (originCube d m))) :
    normalizedL2On (truncatedCube d m j x)
        (fun p => u.toFun p - averageOn (truncatedCube d m j x) u.toFun) ≤
      Real.sqrt (((3 : ℝ) ^ (ell - j + 2)) ^ d) *
        normalizedL2On (truncatedCube d m ell z)
          (fun p => u.toFun p - averageOn (truncatedCube d m ell z) u.toFun) :=
  normalizedL2On_sub_average_crossCentre_le hx hz hjm hellm hsub u

/-! ### The scale obstruction for row 2's oscillation leg -/

/-- The general containment criterion for truncated windows, of which
`Section6Holder.truncatedCube_subset_succ_of_holderGridCentre` is the case
`ell = j + 1`. -/
theorem interiorHolderRegularity_windowContainment {d : ℕ} {m j ell : ℤ}
    {x z : Vec d}
    (hdist : ∀ i : Fin d, |x i - z i| ≤ ((3 : ℝ) ^ ell - (3 : ℝ) ^ j) / 2) :
    truncatedCube d m j x ⊆ truncatedCube d m ell z :=
  truncatedCube_subset_of_dist hdist

/-- **The scale obstruction, certified.**  A scale-`g` grid centre is only
within `3^g / 2` of `x`, so containment of its scale-`ell` window needs
`3^g + 3^j ≤ 3^ell`, which forces `g < ell` for every `j`.  Frozen row 1 ties
the grid scale to the window scale (`OnTriadicGrid ell y` with window
`U_{m,ell}(y)`), so no single containment can carry an off-grid base point to
it: row 2's oscillation leg requires a covering argument, not a containment. -/
theorem interiorHolderRegularity_scaleObstruction {g j ell : ℤ}
    (hcrit : (3 : ℝ) ^ g + (3 : ℝ) ^ j ≤ (3 : ℝ) ^ ell) : g < ell :=
  grid_scale_lt_of_containment_criterion hcrit

/-! ### The energy cover -/

/-- **Energy additivity over a finite cover.**  This is the mechanism the
corrected row-2 architecture needs: energies carry no mean, so covering costs
only the box count.  Contrast the oscillation, where the same move is false
(a smooth step across a grid face has small oscillation on every grid box and
order-one oscillation on a box straddling the face). -/
theorem interiorHolderRegularity_energyCover {d : ℕ} {W : Set (Vec d)} {ι : Type*}
    [DecidableEq ι] {S : Finset ι} {Wf : ι → Set (Vec d)} {g : Vec d → ℝ}
    (hmeas : ∀ y, MeasurableSet (Wf y)) (hg0 : ∀ p, 0 ≤ g p)
    (hint : ∀ y, MeasureTheory.IntegrableOn g (Wf y) MeasureTheory.volume)
    (hcover : W ⊆ ⋃ y ∈ S, Wf y) :
    ∫ p in W, g p ∂MeasureTheory.volume ≤
      ∑ y ∈ S, ∫ p in Wf y, g p ∂MeasureTheory.volume :=
  setIntegral_le_of_cover_finset hmeas hg0 hint hcover

/-- **The energy cover in row 2's own carrier.**  A window covered by finitely
many windows of no larger volume, each with energy seminorm at most `N`, has
energy seminorm at most `√(card) · N`.  This is the discharge route for row 2's
left-hand side at an off-grid base point. -/
theorem interiorHolderRegularity_energyCoverNormalized {d : ℕ}
    {W : Set (Vec d)} {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {Wf : ι → Set (Vec d)} {f : Vec d → Vec d} {N : ℝ}
    (hmeas : ∀ y, MeasurableSet (Wf y))
    (hint : ∀ y, MeasureTheory.IntegrableOn
      (fun p => Homogenization.euclideanNorm (f p) ^ 2) (Wf y)
      MeasureTheory.volume)
    (hcover : W ⊆ ⋃ y ∈ S, Wf y)
    (hWpos : 0 < (MeasureTheory.volume W).toReal)
    (hfin : ∀ y ∈ S, MeasureTheory.volume (Wf y) ≠ ⊤)
    (hvol : ∀ y ∈ S, (MeasureTheory.volume (Wf y)).toReal ≤
      (MeasureTheory.volume W).toReal)
    (hN : ∀ y ∈ S, vectorNormalizedL2On (Wf y) f ≤ N) (hN0 : 0 ≤ N) :
    vectorNormalizedL2On W f ≤ Real.sqrt (S.card : ℝ) * N :=
  vectorNormalizedL2On_le_of_cover_finset hmeas hint hcover hWpos hfin hvol hN hN0

/-! ### The concrete grid cover -/

/-- **The scale-`j` grid windows cover an off-grid window a.e.**  They are open
boxes, so a point on a grid box face lies in none of them; that exceptional set
is a countable union of coordinate hyperplanes, hence null.  This is why the
cover is stated a.e., which is the form the energy cover accepts. -/
theorem interiorHolderRegularity_gridCover (d j m : ℕ) (x : Vec d) (hjm : j ≤ m) :
    truncatedCube d (m : ℤ) (j : ℤ) x ≤ᵐ[MeasureTheory.volume]
      ⋃ y ∈ gridNeighbours d j m x, truncatedCube d (m : ℤ) (j : ℤ) y :=
  truncatedCube_aecover_gridNeighbours d j m x hjm

/-- The grid box faces are null. -/
theorem interiorHolderRegularity_gridFaces_null (d j : ℕ) :
    MeasureTheory.volume (gridFaces d j) = 0 :=
  volume_gridFaces d j

/-- The energy cover under an a.e. cover, in row 2's carrier. -/
noncomputable def interiorHolderRegularity_energyCoverAE (d : ℕ) :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.vectorNormalizedL2On_le_of_aecover_finset d

/-! ### Row 2's left-hand side at an off-grid base point -/

/-- Same-scale truncated windows differ in volume by at most `9^d` — truncation
against the domain means a covering piece can be *larger* than the base window,
so the cover bound needs a ratio, not `≤`. -/
theorem interiorHolderRegularity_windowVolumeRatio {d : ℕ} {m j : ℤ}
    {x y : Vec d} (hx : x ∈ cube d m) (hy : y ∈ cube d m) (hjm : j - 1 ≤ m) :
    (MeasureTheory.volume (truncatedCube d m j y)).toReal ≤
      ((3 : ℝ) ^ (2 : ℤ)) ^ d *
        (MeasureTheory.volume (truncatedCube d m j x)).toReal :=
  volume_truncatedCube_le_ratio hx hy hjm

/-- **Row 2's left-hand side, transferred from the grid neighbours.**  A uniform
energy bound at the scale-`j` grid windows around `x` — where Step 6 and row 1
both apply, the grid scale matching the window scale — gives the bound at the
off-grid window, with the dimension-only factor `√(card · 9^d)`.

This discharges the geometric half of row 2's leg; the uniform bound at the grid
neighbours (Step 6 and the conversion there, with good-centre selection) is what
remains. -/
theorem interiorHolderRegularity_rowTwoOffGrid (d j m : ℕ) (x : Vec d)
    (f : Vec d → Vec d) {N : ℝ} (hjm : j ≤ m) (hx : x ∈ cube d (m : ℤ))
    (hint : ∀ y : Vec d, MeasureTheory.IntegrableOn
      (fun p => Homogenization.euclideanNorm (f p) ^ 2)
      (truncatedCube d (m : ℤ) (j : ℤ) y) MeasureTheory.volume)
    (hN : ∀ y ∈ gridNeighbours d j m x,
      vectorNormalizedL2On (truncatedCube d (m : ℤ) (j : ℤ) y) f ≤ N)
    (hN0 : 0 ≤ N) :
    vectorNormalizedL2On (truncatedCube d (m : ℤ) (j : ℤ) x) f ≤
      Real.sqrt (((gridNeighbours d j m x).card : ℝ) *
        ((3 : ℝ) ^ (2 : ℤ)) ^ d) * N :=
  vectorNormalizedL2On_offGrid_le_of_gridNeighbours d j m x f hjm hx hint hN hN0

/-! ### Step 6 at the grid neighbours -/

/-- **Interior Step 6 with the cell-interiority as an explicit hypothesis.**
The `z ∈ cube d (m-1)` form is too strong for a grid neighbour, which sits up to
`3^n` from the interior base point and so need not be in `cube d (m-1)` at all;
carrying the cell condition directly makes Step 6 applicable there. -/
noncomputable def interiorHolderRegularity_stepSixGate (d : ℕ) [NeZero d] :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorHolderProjectedEnergyGate d

/-- **The Step-6 cell hypothesis holds at every grid neighbour.**  A cell of a
neighbour's window reaches at most `3^{m-1}/2 + 2·3^n + 3^{n-3}/2`, which for
`n ≤ m-5` is well inside `3^m/2`. -/
theorem interiorHolderRegularity_neighbourCells {d : ℕ} {m n : ℤ} {x y : Vec d}
    (hx : x ∈ cube d (m - 1)) (hn : n ≤ m - 5)
    (hxy : ∀ i : Fin d, |x i - y i| ≤ (3 : ℝ) ^ n) :
    ∀ q, q ∈ truncatedCube d m (n - 1) y →
      openCubeAtScale q (n - 3) ⊆ cube d m :=
  neighbour_cells_subset_cube hx hn hxy

/-! ### The selected good scale, and the energy transfer it forces -/

/-- **Energy scale transfer at a fixed centre.**  The good-scale machinery
delivers `goodEvent` only at a *selected* scale near `n`, never at `n` itself
(`Section6Holder.exists_holderGoodScale_le_card`), so row 2 must come down from
the selected scale to its own.  At a fixed centre that is a window inclusion,
priced by the window volume ratio; the price is of the same `exp(Cλ(m-n))` type
the row-1 absorption already handles. -/
theorem interiorHolderRegularity_energyScaleTransfer {d : ℕ} {m n j : ℤ}
    {y : Vec d} {f : Vec d → Vec d}
    (hy : y ∈ cube d m) (hnm : n - 1 ≤ m) (hjm : j - 1 ≤ m) (hnj : n ≤ j)
    (hint : MeasureTheory.IntegrableOn
      (fun p => Homogenization.euclideanNorm (f p) ^ 2)
      (truncatedCube d m j y) MeasureTheory.volume) :
    vectorNormalizedL2On (truncatedCube d m n y) f ≤
      Real.sqrt (((3 : ℝ) ^ (j - n + 2)) ^ d) *
        vectorNormalizedL2On (truncatedCube d m j y) f :=
  vectorNormalizedL2On_scaleTransfer hy hnm hjm hnj hint

/-! ### The stopped failure row at the selection's parameters -/

/-- **The stopped control's bound is exactly what the good-scale selection
needs**, but only at `n_sel = n-2`, `top_sel = m-2`: the shift `j ↦ j+2` carries
the selection's index set onto `Icc n m` and its bound onto `1 + λ(m-n)`, the
control's own.  Any other `top` leaves a gap of the wrong sign. -/
theorem interiorHolderRegularity_shiftedFailureRow {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (epsilon s lambda : ℝ) (n m : ℕ)
    (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hctrl : (∑ i ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M none i z epsilon s then (1 : ℝ) else 0)) <
      1 + lambda * ((m : ℝ) - (n : ℝ))) :
    (∑ j ∈ Finset.Icc (n - 2) (m - 2),
        (1 - if omega ∈ goodEvent M none (j + 2) z epsilon s then (1 : ℝ) else 0)) <
      1 + lambda * (((m - 2 : ℕ) : ℝ) - ((n - 2 : ℕ) : ℝ)) :=
  shifted_failure_row M epsilon s lambda n m z omega hn hm hctrl

/-! ### The selection's room condition, and the `step` it forces -/

/-- The stopping scale is at least `step + 5` — the margin built into
`holderStoppingScale = max (depths) + step + 5`. -/
theorem interiorHolderRegularity_stepMargin {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    step + 5 ≤ Section6Stopping.measurableHolderStoppingScale M alpha lambda
      epsilon step m omega :=
  step_add_five_le_measurableHolderStoppingScale M alpha lambda epsilon step m omega

/-- **The good-scale selection's room condition.**  At the forced parameters it
reads `(k : ℝ) + 1 ≤ (1-λ)(m-n)`, so with `λ ≤ 1/2` it needs `m - n ≥ 2k + 2`;
the only source of that is the stopping scale's `step` margin.  Hence the
selection requires `2k + 2 ≤ step + 5`, and **`step = 0` is inadmissible once
`k ≥ 2`** — while `exists_holderContractionParameters` produces `k = max N 4 ≥ 4`.
The row packages must therefore run at a `step` sized for the selection. -/
theorem interiorHolderRegularity_selectionRoom {k step m n : ℕ} {lambda : ℝ}
    (hlam : lambda ≤ 1 / 2) (hk : 2 * k + 2 ≤ step + 5)
    (hgap : ((step : ℤ) + 5) ≤ (m : ℤ) - (n : ℤ)) :
    (k : ℝ) + 6 + lambda * ((m : ℝ) - (n : ℝ)) ≤ ((m : ℝ) - (n : ℝ)) + 5 :=
  selection_room_of_step hlam hk hgap

/-! ### Row 1 at an arbitrary deterministic margin -/

/-- **Frozen row 1 at any `step`.**  `measurableNatEnvelope` factors through
`toMeasurable`, which is choice-defined and carries no monotonicity, so the
stopping scale is *not* monotone in `step` and the `step = 0` result of
`interiorHolderRegularity_rowOne` cannot be re-read at the larger `step` that
row 2's good-scale selection forces.  Row 1 is therefore re-run with `step`
free; its proof never used more than `X ≥ step + 5`, so this is a re-run and not
new mathematics. -/
noncomputable def interiorHolderRegularity_rowOneAtStep (d : ℕ) [NeZero d] :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorRowOneAtStep d

/-- The gated Campanato output at an arbitrary `step`. -/
noncomputable def interiorHolderRegularity_campanatoOutputAtStep (d : ℕ) [NeZero d] :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorCampanatoOutputAtStep d

/-! ### The good scale at a centre, and the witness offset row 2 forces -/

/-- **The good-scale selection at a grid centre**, at the forced parameters:
failure row from the stopped controls, room from the `step` margin. -/
noncomputable def interiorHolderRegularity_goodScaleAtCentre (d : ℕ) :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_goodScale_at_gridCentre d



theorem interiorHolderRegularity_witnessOffset {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {C C' alpha : ℝ} {c k : ℕ}
    (hC : 0 < C) (hck : c ≤ k) (hCC' : C + (c : ℝ) ≤ C') :
    gammaOneRHS M C alpha (k - c) ≤ gammaOneRHS M C' alpha k :=
  gammaOneRHS_offset M hC hck hCC'

/-! ### Frozen row 2 -/

/-- **The gate scale row 2 runs interior Step 6 at.**  Step 6 reads its good
event six scales above the scale its conclusion lands on, so the selection has to
produce a good scale in the *window* `[n+6, n+6+K]` above the base — the failure
row over `Icc n m` restricts to any sub-window, and a window longer than the
failure budget `K` must contain a good scale. -/
noncomputable def interiorHolderRegularity_rowTwoGateScale (d : ℕ) :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorRowTwoGateScale d

/-- **Interior Step 6 at the gate scale, read at the frozen base scale.**  The
passage down is one window inclusion at a fixed centre, priced by
`scaleTransferPrice`; the Chapter 3 fractional datum carrier is produced from the
frozen Hölder datum at the gate's own order `1/4`. -/
noncomputable def interiorHolderRegularity_rowTwoGateBudget (d : ℕ) [NeZero d] :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorRowTwoGateBudget d

/-- **Row 2's oscillation leg.**  The off-grid transfer to a scale-`n` grid
centre *of `cu_{m-1}`*, the printed Campanato family (D-068) at the gate scale,
and the top-window energy compose into a single
`Kpre · exp(A₀ + P·λ·(m-n+1))` times the frozen right-hand side.  No pathwise
ellipticity bound is used: the good-scale cap is `EllipticityCap`. -/
noncomputable def interiorHolderRegularity_rowTwoOscLeg (d : ℕ) [NeZero d] :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorRowTwoOscLeg d

/-- **Row 2's forcing leg.**  The Besov/Hölder embedding at the gate window
against the frozen datum, with the coefficient pairing supplying
`σ^{-1/2} ≤ exp(Cλ(m-n)) b^{-1/2}`. -/
noncomputable def interiorHolderRegularity_rowTwoForcingLeg (d : ℕ) [NeZero d] :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.interiorRowTwo_forcingLeg d

/-- **Frozen row 2 for the interior anchor is closed**, conditional only on
`InteriorHolderExcessDecayInput`.

The stopping parameters are returned with `2 ≤ C₁ ≤ C₂`, which is what makes the
three model-side conditions `0 ≤ λ`, `λ < 1` and `ε⁸ ≤ λ` *theorems* rather than
hypotheses; only the two conditions that genuinely couple `δ` to the `alpha`
window — `ε ∈ Icc (s⁻¹δ²) 1` and `δ² ≤ λ` — are still carried.  The deterministic
margin must satisfy `step ≥ 21`: the gate selection and the top selection
together consume `2K + 11` scales above the base, with
`K = ⌈λ(m-n)⌉ ≤ (m-n)/4 + 1`. -/
noncomputable def interiorHolderRegularity_rowTwo (d : ℕ) [NeZero d] :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorRowTwoAtStep d

/-! ### One stopping scale for all three rows -/

/-- **The three rows with free stopping parameters.**  Each row originally
pinned its own `(C₁, C₂)` — row 1 from `exists_holderExponentialAbsorption` and
`exists_holderContractionParameters`, row 2 at `max C₁abs 2`, row 3 at its own
contraction constant — so no single stopping scale served all three.  Each is
re-run with the parameters universally quantified above their thresholds; the
only proof changes are the two monotonicity steps (`C₁` enlargement in the
absorption, `C₂` enlargement in the contraction clause). -/
noncomputable def interiorHolderRegularity_rowOneFree (d : ℕ) [NeZero d] :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorRowOneAtStepFree d

/-- See `interiorHolderRegularity_rowOneFree`. -/
noncomputable def interiorHolderRegularity_rowTwoFree (d : ℕ) [NeZero d] :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorRowTwoAtStepFree d

/-- See `interiorHolderRegularity_rowOneFree`. -/
noncomputable def interiorHolderRegularity_rowThreeFree (d : ℕ) [NeZero d] :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorRowThreeAtStepFree d

/-- **The three model-free stopping conditions are theorems** at any coupled
pair `2 ≤ C₁ ≤ C₂`.  This is what lets the row packages carry only the two
conditions that genuinely tie `delta` to the `alpha`-window. -/
theorem interiorHolderRegularity_stoppingConditions {C1 C2 alpha : ℝ}
    (hC1 : 2 ≤ C1) (hC1C2 : C1 ≤ C2)
    (halpha : alpha ∈ Set.Icc (1 / 2 : ℝ) 1) :
    0 ≤ Section6Stopping.holderStoppingLambda C1 alpha ∧
      Section6Stopping.holderStoppingLambda C1 alpha < 1 ∧
      Section6Stopping.holderStoppingEpsilon C2 alpha ^ 8 ≤
        Section6Stopping.holderStoppingLambda C1 alpha :=
  holderStopping_conditions_of_coupled hC1 hC1C2 halpha

/-- **The four model-side stopping conditions, from the frozen window alone.**
`delta ≤ C⁻¹` and `alpha ≤ 1 - C·delta·|log delta|^{1/2}` give
`1 - alpha ≥ C·delta` (because `delta ≤ 1/46` forces `|log delta| ≥ 1`), and
from that both `epsilon ∈ Icc (s⁻¹delta²) 1` and `delta² ≤ lambda` follow once
`C ≥ 46`, `C ≥ C₁` and `C ≥ 1024 C₂²`.  There is no degenerate `delta = 0`
endpoint: `0 < delta` is part of the model. -/
theorem interiorHolderRegularity_modelConditions {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {C C1 C2 alpha : ℝ}
    (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) (hC46 : 46 ≤ C) (hCC1 : C1 ≤ C)
    (hCC2 : 1024 * C2 ^ 2 ≤ C) (hdelta : M.delta ≤ C⁻¹)
    (halpha : alpha ∈ Set.Icc (1 / 2 : ℝ)
      (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ))) :
    64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS ∧
      alpha ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
      Section6Stopping.holderStoppingEpsilon C2 alpha ∈
        Set.Icc (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1 ∧
      M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha :=
  holderStopping_model_conditions M hC1 hC2 hC46 hCC1 hCC2 hdelta halpha

/-- **The whole frozen conclusion package, at one stopping scale, for every
`m ≤ L`.**  The three rows share the pair `(C₁, C₂)` with `2 ≤ C₁ ≤ C₂` and the
deterministic margin `step ≥ 21`, and the carrier is the *cutoff-independent*
`measurableHolderStoppingScale`. -/
noncomputable def interiorHolderRegularity_rowsAboveCutoff (d : ℕ) [NeZero d] :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorRowsAboveCutoff d

/-! ### What the `L < m` branch already has -/



theorem interiorHolderRegularity_tailSaturation {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    tailAverage M L m ω (cube d (m : ℤ)) = ahom M L :=
  tailAverage_cube_eq_ahom_of_cutoff_le M hLm ω



theorem interiorHolderRegularity_bRatioSaturated {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L q m : ℕ} (hLq : L ≤ q)
    (hLm : L ≤ m) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d) :
    tailAverage M L q ω (translatedCube d (q : ℤ) z) /
          tailAverage M L m ω (cube d (m : ℤ)) = 1 ∧
      tailAverage M L m ω (cube d (m : ℤ)) /
          tailAverage M L q ω (translatedCube d (q : ℤ) z) = 1 :=
  tailAverage_ratio_eq_one_of_cutoff_le_scales M hLq hLm ω z

/-! ### The `L < m` residual -/



abbrev InteriorRowsBelowCutoff (d : ℕ) : Prop :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.InteriorRowsBelowCutoff d

/-- **Both frozen sample-space packages from one carrier.**  The frozen conjuncts
ask only for *some* measurable witness, so the fixed-cutoff conjunct may also use
the cutoff-independent stopping scale.  Two consequences: the finite-cutoff Γ₁
tail is no longer needed (one tail serves both), and the `(some L)` versus `none`
mismatch between `measurableCutoffHolderStoppingScale` and the landed rows
disappears. -/
noncomputable def interiorHolderRegularity_oneCarrier (d : ℕ) :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.interiorCutoffPathwiseInput_of_uncutTailAndRows d

/-- **The frozen interior anchor, from the excess-decay premise and the `L < m`
residual alone.**  Every probabilistic obligation, the whole outer four-conjunct
surface, the stopping-parameter coupling, the model-parameter window and the
`m ≤ L` branch of all three rows are discharged. -/
theorem exists_cutoffHolderRegularityInterior_of_excessDecay (d : ℕ) [NeZero d]
    (hExcess : InteriorHolderExcessDecayInput d)
    (hbelow : InteriorRowsBelowCutoff d) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      (M.delta ≤ C⁻¹ →
      ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
        ∀ L m : ℕ,
          (∃ X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
            Measurable X ∧ (∀ ω, 0 < X ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ ω, ∀ (u : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d),
              IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
                  (cube d m) u g →
              MemHolder (cube d m) (1 / 2) g →
              InteriorHolderRegularityConclusions M C L ω alpha m (X ω) u g) ∧
          (m ≤ L → ∃ Xuncut : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
            Measurable Xuncut ∧ (∀ ω, 0 < Xuncut ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xuncut ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ J : ℕ, m ≤ J → ∀ ω,
              ∀ (u : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M J ω)
                    (cube d m) u g →
                MemHolder (cube d m) (1 / 2) g →
                InteriorHolderRegularityConclusions M C J ω alpha m (Xuncut ω) u g) ∧
          ∀ y : Vec d,
            (∃ Xy : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
              Measurable Xy ∧ (∀ ω, 0 < Xy ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xy ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ ω, ∀ (u : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDivFormWeakSolutionOn
                    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
                      (translatePotentialSample y ω))
                    (cube d m) u g →
                MemHolder (cube d m) (1 / 2) g →
                InteriorHolderRegularityConclusions M C L (translatePotentialSample y ω)
                  alpha m (Xy ω) u g) ∧
            (m ≤ L → ∃ XuncutY : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
              Measurable XuncutY ∧ (∀ ω, 0 < XuncutY ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < XuncutY ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ J : ℕ, m ≤ J → ∀ ω,
                ∀ (u : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d),
                  IsDivFormWeakSolutionOn
                      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M J
                        (translatePotentialSample y ω))
                      (cube d m) u g →
                  MemHolder (cube d m) (1 / 2) g →
                  InteriorHolderRegularityConclusions M C J (translatePotentialSample y ω)
                    alpha m (XuncutY ω) u g)) :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_cutoffHolderRegularityInterior_of_excess_and_below
    d hExcess hbelow

/-! ### The interior cutoff Hölder anchor, unconditional -/



theorem exists_cutoffHolderRegularityInterior (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      (M.delta ≤ C⁻¹ →
      ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
        ∀ L m : ℕ,
          (∃ X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
            Measurable X ∧ (∀ ω, 0 < X ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ ω, ∀ (u : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d),
              IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
                  (cube d m) u g →
              MemHolder (cube d m) (1 / 2) g →
              InteriorHolderRegularityConclusions M C L ω alpha m (X ω) u g) ∧
          (m ≤ L → ∃ Xuncut : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
            Measurable Xuncut ∧ (∀ ω, 0 < Xuncut ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xuncut ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ J : ℕ, m ≤ J → ∀ ω,
              ∀ (u : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M J ω)
                    (cube d m) u g →
                MemHolder (cube d m) (1 / 2) g →
                InteriorHolderRegularityConclusions M C J ω alpha m (Xuncut ω) u g) ∧
          ∀ y : Vec d,
            (∃ Xy : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
              Measurable Xy ∧ (∀ ω, 0 < Xy ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xy ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ ω, ∀ (u : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDivFormWeakSolutionOn
                    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
                      (translatePotentialSample y ω))
                    (cube d m) u g →
                MemHolder (cube d m) (1 / 2) g →
                InteriorHolderRegularityConclusions M C L (translatePotentialSample y ω)
                  alpha m (Xy ω) u g) ∧
            (m ≤ L → ∃ XuncutY : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
              Measurable XuncutY ∧ (∀ ω, 0 < XuncutY ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < XuncutY ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ J : ℕ, m ≤ J → ∀ ω,
                ∀ (u : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d),
                  IsDivFormWeakSolutionOn
                      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M J
                        (translatePotentialSample y ω))
                      (cube d m) u g →
                  MemHolder (cube d m) (1 / 2) g →
                  InteriorHolderRegularityConclusions M C J (translatePotentialSample y ω)
                    alpha m (XuncutY ω) u g)) :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.exists_cutoffHolderRegularityInterior_of_excessPair
    d
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecayInterior.interiorHolderExcessDecayInput_of_interiorHarmonic
      d (fun [NeZero d] =>
        SubdiffusiveProcess.Frozen.Section6.harmonic_approximation_good_scales_interior d))
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.interiorCutoffHolderExcessDecayInput_of_interiorCutoffHarmonic
      d (-2 : ℝ) (-8 : ℝ) (fun [NeZero d] =>
        SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.interiorCutoffHarmonicApproximationInput_holds d))







theorem cutoff_holder_regularity_interior
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      (M.delta ≤ C⁻¹ →
      ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
        ∀ L m : ℕ,
          (∃ X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
            Measurable X ∧ (∀ ω, 0 < X ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ ω, ∀ (u : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d),
              IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
                  (cube d m) u g →
              MemHolder (cube d m) (1 / 2) g →
              InteriorHolderRegularityConclusions M C L ω alpha m (X ω) u g) ∧
          (m ≤ L → ∃ Xuncut : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
            Measurable Xuncut ∧ (∀ ω, 0 < Xuncut ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xuncut ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ J : ℕ, m ≤ J → ∀ ω,
              ∀ (u : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M J ω)
                    (cube d m) u g →
                MemHolder (cube d m) (1 / 2) g →
                InteriorHolderRegularityConclusions M C J ω alpha m (Xuncut ω) u g) ∧
          ∀ y : Vec d,
            (∃ Xy : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
              Measurable Xy ∧ (∀ ω, 0 < Xy ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xy ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ ω, ∀ (u : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDivFormWeakSolutionOn
                    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
                      (translatePotentialSample y ω))
                    (cube d m) u g →
                MemHolder (cube d m) (1 / 2) g →
                InteriorHolderRegularityConclusions M C L (translatePotentialSample y ω)
                  alpha m (Xy ω) u g) ∧
            (m ≤ L → ∃ XuncutY : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
              Measurable XuncutY ∧ (∀ ω, 0 < XuncutY ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < XuncutY ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ J : ℕ, m ≤ J → ∀ ω,
                ∀ (u : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d),
                  IsDivFormWeakSolutionOn
                      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M J
                        (translatePotentialSample y ω))
                      (cube d m) u g →
                  MemHolder (cube d m) (1 / 2) g →
                  InteriorHolderRegularityConclusions M C J (translatePotentialSample y ω)
                    alpha m (XuncutY ω) u g)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨1, one_pos, fun M => absurd M.shellPrefix.dimension (by norm_num)⟩
  · haveI : NeZero d := ⟨hd.ne'⟩
    exact exists_cutoffHolderRegularityInterior d


end

end SubdiffusiveProcess.Providers.Section6
