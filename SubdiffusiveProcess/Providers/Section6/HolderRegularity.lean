module

public import SubdiffusiveProcess.Section6.GoodScaleMathcalE
public import SubdiffusiveProcess.Section6.DensityOfGoodScales
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.HolderScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.GoodDensityTranslation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.ErrorStoppingAnalytic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.StoppedRatio
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.LocalMathcalE
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.WindowSeminorms
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ExcessDecayInput
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ParameterAbsorption
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.DimensionZero
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.CampanatoRebaseArithmetic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ExcessRebaseArithmetic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.InternalExport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ProjectedEnergyAssembly
public import SubdiffusiveProcess.Providers.Section6.ExcessDecayGoodScales
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.HarmonicPassages
public import SubdiffusiveProcess.Providers.Section6.CutoffHolderRegularity

@[expose] public section




namespace SubdiffusiveProcess.Providers.Section6

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Provider-local name retained for the exact provisional conclusion consumed
by the Hölder ladder. -/
abbrev HolderExcessDecayInput (d : ℕ) : Prop :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.HolderExcessDecayInput d

/-- The audited density anchor discharges the former quarantined stopping
input by one exact application. -/
theorem densityOfGoodScalesInput_of_proved (d : ℕ) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.DensityOfGoodScalesInput d := by
  exact _root_.SubdiffusiveProcess.Section6.density_of_good_scales d

/-- The proved `p.good.scale.mathcal.E` supplies the exact cap input formerly
carried as the second premise of the excess-decay provider. -/
theorem mathcalECapInput_of_goodScale (d : ℕ) : MathcalECapInput d := by
  obtain ⟨C, hC, hgood⟩ := _root_.SubdiffusiveProcess.Section6.good_scale_mathcal_e d
  refine ⟨C, hC, ?_⟩
  intro M s hs L m hmL ω epsilon hepsilon hω
  exact (hgood M s hs L m hmL ω).2 epsilon hepsilon hω

/-- Once the harmonic-approximation conclusion is supplied, the established
conditional excess-decay provider yields exactly the sole draft input used by
the Hölder spine. -/
theorem holderExcessDecayInput_of_harmonicApproximation (d : ℕ)
    (hharm : HarmonicApproximationInput d) : HolderExcessDecayInput d := by
  exact excess_decay_good_scales_of_anchors d hharm (mathcalECapInput_of_goodScale d)

/-- Steps 1--2 after fixing `s₀ = 1/32`,
`lambda = C₁⁻¹(1-alpha)`, and
`epsilon = C₂⁻¹ sqrt(1-alpha)`: the literal combined stopping scale is
strictly positive and, beyond it, both pathwise controls used by the Hölder
iteration hold at every admissible grid centre. -/
theorem holderRegularity_stopping_controls {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (C1 C2 alpha : ℝ)
    (step m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    let X := Section6Stopping.holderStoppingScale M alpha
      (Section6Stopping.holderStoppingLambda C1 alpha)
      (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega
    0 < X ∧
      ∀ n : ℕ, (X : ℤ) ≤ (m : ℤ) - (n : ℤ) →
        ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d m →
          (∑ j ∈ Finset.Icc n m,
              accumulatedError M none j z Section6Stopping.holderStoppingS omega) ≤
              Section6Stopping.holderStoppingLambda C1 alpha *
                ((m : ℝ) - (n : ℝ)) ∧
            (∑ j ∈ Finset.Icc n m,
                (1 - if omega ∈ goodEvent M none j z
                  (Section6Stopping.holderStoppingEpsilon C2 alpha)
                  Section6Stopping.holderStoppingS then 1 else 0)) <
              1 + Section6Stopping.holderStoppingLambda C1 alpha *
                ((m : ℝ) - (n : ℝ)) := by
  dsimp only
  refine ⟨Section6Stopping.holderStoppingScale_pos M alpha
    (Section6Stopping.holderStoppingLambda C1 alpha)
    (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega, ?_⟩
  intro n hn z hzgrid hzmem
  exact Section6Stopping.holder_stopped_controls_at_parameters
    M C1 C2 alpha step m n omega hn z hzgrid hzmem

/-- Measurable replacement of the combined stopping depth.  This is the
exact package consumed by the first three binders of the frozen conclusion,
apart from the quantitative Gamma-one tail estimate itself. -/
theorem holderRegularity_measurable_stopping_controls {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (C1 C2 alpha : ℝ)
    (step m : ℕ) :
    let X := Section6Stopping.measurableHolderStoppingScale M alpha
      (Section6Stopping.holderStoppingLambda C1 alpha)
      (Section6Stopping.holderStoppingEpsilon C2 alpha) step m
    Measurable X ∧ (∀ omega, 0 < X omega) ∧
      ∀ omega, ∀ n : ℕ, (X omega : ℤ) <= (m : ℤ) - (n : ℤ) ->
        ∀ z : Vec d, OnTriadicGrid n z -> z ∈ cube d m ->
          (∑ j ∈ Finset.Icc n m,
              accumulatedError M none j z Section6Stopping.holderStoppingS omega) <=
              Section6Stopping.holderStoppingLambda C1 alpha *
                ((m : ℝ) - (n : ℝ)) ∧
            (∑ j ∈ Finset.Icc n m,
                (1 - if omega ∈ goodEvent M none j z
                  (Section6Stopping.holderStoppingEpsilon C2 alpha)
                  Section6Stopping.holderStoppingS then 1 else 0)) <
              1 + Section6Stopping.holderStoppingLambda C1 alpha *
                ((m : ℝ) - (n : ℝ)) := by
  dsimp only
  refine ⟨Section6Stopping.measurable_measurableHolderStoppingScale
    M alpha (Section6Stopping.holderStoppingLambda C1 alpha)
      (Section6Stopping.holderStoppingEpsilon C2 alpha) step m,
    fun omega => Section6Stopping.measurableHolderStoppingScale_pos
      M alpha (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega, ?_⟩
  intro omega n hn z hzgrid hzmem
  exact Section6Stopping.measurableHolder_stopped_controls_at_parameters
    M C1 C2 alpha step m n omega hn z hzgrid hzmem

/-- The completed probabilistic half of `l.sum.the.errors`, at the fixed
Hölder scale `s0 = 1/32`. -/
theorem exists_holderRegularity_errorStopping_tail {d : ℕ} [NeZero d] :
    ∃ K C : ℝ, 1 ≤ K ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ K⁻¹ →
      ∀ lambda : ℝ,
        Section6Stopping.holderErrorSpatialCoeff d C * M.delta *
            Real.sqrt |Real.log M.delta| ≤ lambda →
        ∀ q m : ℕ, 0 < q →
          M.P.toMeasure.real {omega |
              q < Section6Stopping.errorStoppingDepth M lambda
                Section6Stopping.holderStoppingS m omega} ≤
            Section6Stopping.holderGammaOneGeometricConst * Real.exp
              (-(lambda ^ 2 * max ((q : ℝ) - 1) 0 /
                (Section6Stopping.holderErrorSpatialCoeff d C ^ 2 *
                  M.delta ^ 2 * |Real.log M.delta|))) := by
  exact Section6Stopping.exists_errorStoppingDepth_tail (d := d)

private theorem zero_onTriadicGrid {d n : ℕ} : OnTriadicGrid n (0 : Vec d) := by
  intro i
  exact ⟨0, by simp⟩

/-- The stopped controls instantiated in the completed coefficient-ratio
assembly.  This is `e.ratio.of.bs` with the Hölder parameters substituted and
with the manuscript's linear-in-window exponential retained. -/
theorem holderRegularity_tailAverage_ratio {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (C1 C2 alpha : ℝ)
    (step L n q m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hnm : n < m) (hnq : n ≤ q) (hqm : q ≤ m) (hmL : m ≤ L)
    (hn : (Section6Stopping.measurableHolderStoppingScale M alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : Int) ≤
      (m : Int) - (n : Int))
    (z : Vec d) (hzgrid : OnTriadicGrid n z) (hz : z ∈ cube d m)
    (hlambda0 : 0 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (hlambda1 : Section6Stopping.holderStoppingLambda C1 alpha < 1)
    (hepsilon0 : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha)
    (hdelta : M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha) :
    let C := 4 * (d : ℝ) +
      ((3 : ℝ) ^ (-(Section6Stopping.holderStoppingS / 8)))⁻¹ + 1
    tailAverage M L q omega (translatedCube d (q : ℤ) z) /
        tailCoefficientCubeAverage M L m omega ≤
      Real.exp (C * Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (n : ℝ))) ∧
    tailCoefficientCubeAverage M L m omega /
        tailAverage M L q omega (translatedCube d (q : ℤ) z) ≤
      Real.exp (C * Section6Stopping.holderStoppingLambda C1 alpha *
        ((m : ℝ) - (n : ℝ))) := by
  have hcontrolsZ := Section6Stopping.measurableHolder_stopped_controls_at_parameters
    M C1 C2 alpha step m n omega hn z hzgrid hz
  have hzero : (0 : Vec d) ∈ cube d m :=
    Section6ExcessDecay.zero_mem_cube d (m : ℤ)
  have hcontrols0 := Section6Stopping.measurableHolder_stopped_controls_at_parameters
    M C1 C2 alpha step m n omega hn 0 zero_onTriadicGrid hzero
  exact Section6Holder.stopped_tailAverage_ratio_bounds_exp M hnm hnq hqm hmL
    (Section6Stopping.holderStoppingEpsilon C2 alpha)
    Section6Stopping.holderStoppingS
    (Section6Stopping.holderStoppingLambda C1 alpha) hepsilon0
    (by rw [Section6Stopping.holderStoppingS]; norm_num)
    hlambda0 hlambda1 hdelta omega z hz
    hcontrolsZ.1 hcontrols0.1 hcontrolsZ.2 hcontrols0.2

/-- Steps 3--5 on the exact draft excess-decay input: the concrete recurrence
families, interval sums, bad-scale set, and the proved iteration lemma have
already been composed.  The returned estimate is the full-domain Campanato
row before the final `C₁` absorption and off-grid rebasing. -/
theorem holderRegularity_campanatoFull {d : ℕ} [NeZero d]
    (hExcess : HolderExcessDecayInput d) :
    ∃ Cstep K Citer : ℝ, 0 < Cstep ∧ 0 < K ∧ 0 < Citer ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ epsilon ∈ Set.Icc
          (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1,
      ∀ lambda : ℝ, 0 ≤ lambda → M.delta ^ 2 ≤ lambda → epsilon ^ 8 ≤ lambda →
      ∀ k : ℕ, 0 < k → ∀ theta ∈ Set.Ioo (0 : ℝ) 1,
      theta ^ k ∈ Set.Ioo (0 : ℝ) (3 / 5) →
      Cstep * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
          (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * epsilon) ≤ theta ^ k →
      ∀ L domain n top : ℕ, n < top → top + 5 ≤ domain → domain ≤ L →
      ∀ z ∈ cube d domain,
      ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      (∑ i ∈ Finset.Icc n domain,
          accumulatedError M none i z Section6Stopping.holderStoppingS omega) ≤
        lambda * ((domain : ℝ) - (n : ℝ)) →
      (∑ i ∈ Finset.Icc n domain,
          ((1 : ℝ) - if omega ∈ goodEvent M none i z epsilon
            Section6Stopping.holderStoppingS then 1 else 0)) <
        1 + lambda * ((domain : ℝ) - (n : ℝ)) →
      ∀ exponential : ℝ, 0 ≤ exponential →
      (∀ j ∈ Finset.Icc n top,
        tailCoefficientCubeAverage M L domain omega /
            tailAverage M L (j + 2) omega (translatedCube d (j + 2 : ℕ) z) ≤
          exponential) →
      ∀ (u h : H1Function (openCubeSet (originCube d domain))) (g : Vec d → Vec d),
      IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (originCube d domain) u h g →
      MemHolder (cube d domain) (1 / 2) g →
      MemHolder (cube d domain) (1 / 2) h.grad →
      let Keps := Cstep * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
        (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * K
      let Kforce := Cstep * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
        Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4 : ℝ)
      let Kmean := (1 / 4 : ℝ) ^ (-3 / 2 : ℝ)
      let Kboundary := Cstep * (1 / 4 : ℝ) ^ (-3 : ℤ) *
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
      let topForcing := (tailCoefficientCubeAverage M L domain omega)⁻¹ *
        (3 : ℝ) ^ ((domain : ℝ) / 2) *
        holderSeminormOn (cube d domain) (1 / 2) g
      let topBoundary := (3 : ℝ) ^ ((domain : ℝ) / 2) *
        holderSeminormOn (cube d domain) (1 / 2) h.grad
      let boundaryTop :=
        if BoundaryTouches (truncatedCube d domain top z) (cube d domain) then (1 : ℝ) else 0
      let Ebudget := 3 * Keps * lambda * ((domain : ℝ) - (n : ℝ) + 1)
      let Dbudget :=
        (5 / 2 : ℝ) * Kforce *
            (3 : ℝ) ^ (-(((domain : ℝ) - (top : ℝ)) / 2)) *
            exponential * topForcing +
          Kmean * Ebudget * vectorSupNormOn (cube d domain) h.grad * boundaryTop +
          (5 / 2 : ℝ) * Kboundary *
            (3 : ℝ) ^ (-(((domain : ℝ) - (top : ℝ)) / 2)) *
            topBoundary * boundaryTop
      let Abar := Citer * (k + 1) *
          ((k : ℝ) + 2 + lambda * ((domain : ℝ) - (n : ℝ))) +
        Citer * Ebudget
      (3 : ℝ) ^ (-(n : ℤ)) *
          normalizedL2On (truncatedCube d domain n z)
            (fun x ↦ u.toFun x - averageOn (truncatedCube d domain n z) u.toFun) ≤
        Real.exp Abar *
          ((3 : ℝ) ^ (-(top : ℤ)) *
              normalizedL2On (truncatedCube d domain top z)
                (fun x ↦ u.toFun x - averageOn
                  (truncatedCube d domain top z) u.toFun) + Dbudget) :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.exists_holderCampanatoFull d hExcess

/-- The frozen three-row conclusion has no exceptional zero-dimensional
case; it is automatic there and therefore does not enter the analytic
iteration branch. -/
theorem holderRegularityConclusions_dim_zero
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 0) (C : ℝ) (hC : 0 ≤ C)
    (L : ℕ) (ω : _root_.SubdiffusiveProcess.Model.PotentialSample 0) (alpha : ℝ)
    (m X : ℕ) (u h : H1Function (openCubeSet (originCube 0 m)))
    (g : Vec 0 → Vec 0) :
    HolderRegularityConclusions M C L ω alpha m X u h g := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.holderRegularityConclusions_dim_zero (M := M) (C := C) (hC := hC) (L := L) (ω := ω) (alpha := alpha) (m := m) (X := X) (u := u) (h := h) (g := g)


/-- Byte-exact body of frozen `p.cutoff.Holder.regularity` v2, retained as
an explicit hypothesis so this provider never imports the draft anchor. -/
def CutoffHolderRegularityInput (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      (M.delta ≤ C⁻¹ →
      ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
        ∀ L m : ℕ,
          (∃ X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
            Measurable X ∧ (∀ ω, 0 < X ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ ω, ∀ (u h : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d),
              IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) (originCube d m) u h g →
              MemHolder (cube d m) (1 / 2) g →
              MemHolder (cube d m) (1 / 2) h.grad →
              HolderRegularityConclusions M C L ω alpha m (X ω) u h g) ∧
          -- “may take equal” is
          -- rendered by existence of one witness compatible with the
          -- uncutoff conclusion, not by an identity forced on every witness.
          (m ≤ L → ∃ Xuncut : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
            Measurable Xuncut ∧ (∀ ω, 0 < Xuncut ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xuncut ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ J : ℕ, m ≤ J → ∀ ω,
              ∀ (u h : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M J ω) (originCube d m) u h g →
                MemHolder (cube d m) (1 / 2) g →
                MemHolder (cube d m) (1 / 2) h.grad →
                HolderRegularityConclusions M C J ω alpha m (Xuncut ω) u h g) ∧
          ∀ y : Vec d,
            (∃ Xy : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
              Measurable Xy ∧ (∀ ω, 0 < Xy ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xy ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ ω, ∀ (u h : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDirichletSolutionOn
                    (_root_.SubdiffusiveProcess.Model.aCutoff M L
                      (translatePotentialSample y ω))
                    (originCube d m) u h g →
                MemHolder (cube d m) (1 / 2) g →
                MemHolder (cube d m) (1 / 2) h.grad →
                HolderRegularityConclusions M C L (translatePotentialSample y ω) alpha m
                  (Xy ω) u h g) ∧
            (m ≤ L → ∃ XuncutY : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
              Measurable XuncutY ∧ (∀ ω, 0 < XuncutY ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < XuncutY ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ J : ℕ, m ≤ J → ∀ ω,
                ∀ (u h : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d),
                  IsDirichletSolutionOn
                      (_root_.SubdiffusiveProcess.Model.aCutoff M J
                        (translatePotentialSample y ω))
                      (originCube d m) u h g →
                  MemHolder (cube d m) (1 / 2) g →
                  MemHolder (cube d m) (1 / 2) h.grad →
                  HolderRegularityConclusions M C J (translatePotentialSample y ω) alpha m
                    (XuncutY ω) u h g))

/-- The uncutoff Hölder anchor is the cutoff anchor's cutoff-independent
conjunct, instantiated mechanically at `L = m`. -/
theorem holder_regularity_of_cutoff_holder_regularity (d : ℕ)
    (hcutoff : CutoffHolderRegularityInput d) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      (M.delta ≤ C⁻¹ →
      ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
        ∀ m : ℕ, ∃ X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
          Measurable X ∧ (∀ ω, 0 < X ω) ∧
          (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ ENNReal.ofReal
            (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
              (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
          ∀ L : ℕ, m ≤ L → ∀ ω,
            ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
              IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) (originCube d m) u h g →
              MemHolder (cube d m) (1 / 2) g →
              MemHolder (cube d m) (1 / 2) h.grad →
              HolderRegularityConclusions M C L ω alpha m (X ω) u h g) := by
  obtain ⟨C, hC, hall⟩ := hcutoff
  refine ⟨C, hC, ?_⟩
  intro M hdelta alpha halpha m
  exact (hall M hdelta alpha halpha m m).2.1 le_rfl





theorem holder_regularity
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      (M.delta ≤ C⁻¹ →
      ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
        ∀ m : ℕ, ∃ X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
          Measurable X ∧ (∀ ω, 0 < X ω) ∧
          (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ ENNReal.ofReal
            (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
              (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
          ∀ L : ℕ, m ≤ L → ∀ ω,
            ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
              IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) (originCube d m) u h g →
              MemHolder (cube d m) (1 / 2) g →
              MemHolder (cube d m) (1 / 2) h.grad →
              HolderRegularityConclusions M C L ω alpha m (X ω) u h g)

:= holder_regularity_of_cutoff_holder_regularity d
    (SubdiffusiveProcess.Providers.Section6.cutoff_holder_regularity d)



end

end SubdiffusiveProcess.Providers.Section6
