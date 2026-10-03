module

public import SubdiffusiveProcess.CoarseGrainingVocab.NullLagrangianTrace

@[expose] public section




namespace SubdiffusiveProcess.Providers.Section5

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

noncomputable section

private noncomputable def scalarCoeffOnData_const_mul {d : ℕ}
    {U : Ch02.Domain d} {a : Homogenization.Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    {c : ℝ} (hc : 0 < c) : ScalarCoeffOnData U (fun x => c * a x) where
  lam := c * ha.lam
  Lam := c * ha.Lam
  lam_pos := mul_pos hc ha.lam_pos
  lam_le_Lam := mul_le_mul_of_nonneg_left ha.lam_le_Lam hc.le
  aeStronglyMeasurable := by
    intro i j
    have h := (ha.aeStronglyMeasurable i j).const_smul c
    convert h using 1
    funext x
    by_cases hx : x ∈ (U : Set (Homogenization.Vec d))
    · simp [restrictCoeffField, hx, scalarCoeffField, scalarMatrix, mul_assoc]
    · simp [restrictCoeffField, hx, scalarCoeffField]
  aeBounds := by
    filter_upwards [ha.aeBounds] with x hx
    exact ⟨mul_le_mul_of_nonneg_left hx.1 hc.le,
      mul_le_mul_of_nonneg_left hx.2 hc.le⟩

private theorem aMatrix_const_mul {d : ℕ} {U : Ch02.Domain d}
    {a : Homogenization.Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    {c : ℝ} (hc : 0 < c) :
    aMatrix U (scalarCoeffOnData_const_mul ha hc).toCoeffOn =
      c • aMatrix U ha.toCoeffOn := by
  let hb := scalarCoeffOnData_const_mul ha hc
  have hscaled : Ch02.CoeffOn.AEScaled c ha.toCoeffOn hb.toCoeffOn := by
    exact Filter.Eventually.of_forall fun x => by
      ext i j
      simp [hb, scalarCoeffOnData_const_mul, ScalarCoeffOnData.toCoeffOn,
        scalarCoeffField, scalarMatrix, mul_assoc]
  have hhom :=
    (Ch02.responseSubadditivityAndScalingTheory U ha.toCoeffOn).sigma_homogeneous
      hc hscaled
  have htheoryA :=
    Ch02.responseSymmetricDirichletNeumannTheory U ha.toCoeffOn ha.isSymmetric
  have htheoryB :=
    Ch02.responseSymmetricDirichletNeumannTheory U hb.toCoeffOn hb.isSymmetric
  change Ch02.aCoarse U hb.toCoeffOn = c • Ch02.aCoarse U ha.toCoeffOn
  rw [htheoryB.derived_matrices.1, htheoryA.derived_matrices.1]
  exact hhom

private theorem integrable_trace_randomAMatrix {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (U : Ch02.Domain d) :
    Integrable (fun ω => Matrix.trace (randomAMatrix M m U ω)) M.P.toMeasure := by
  unfold Matrix.trace
  exact integrable_finset_sum Finset.univ fun i _hi =>
    ((integrable_randomAMatrix M m U).eval i).eval i

private theorem finiteVolume_reciprocal_lower {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m n : ℕ) :
    Real.exp (-(m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤
      abarScalarReadout M m n := by
  let U := Ch02.cubeDomain (originCube d (n : ℤ))
  let T := negatePotentialSequence (d := d)
  let t : ℝ := (m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  let s : ℝ := Real.exp t
  have hs : 0 < s := Real.exp_pos t
  have hd : 2 ≤ d := M.shellPrefix.dimension
  have hpath : ∀ ω, 2 * (d : ℝ) ≤
      s * (Matrix.trace (randomAMatrix M m U ω) +
        Matrix.trace (randomAMatrix M m U (T ω))) := by
    intro ω
    let hω := aCutoffCoeffOnData M m ω U
    let hTω := aCutoffCoeffOnData M m (T ω) U
    let hc := scalarCoeffOnData_const_mul hω hs
    let hcT := scalarCoeffOnData_const_mul hTω hs
    have hfun :
        (fun x => s * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m (T ω) x) =
          (fun x => (s * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m ω x)⁻¹) := by
      funext x
      exact uncenteredCutoff_negatePotentialSequence M m ω x
    let hcInv : ScalarCoeffOnData U
        (fun x => (s * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m ω x)⁻¹) :=
      hfun ▸ hcT
    have htrace := SubdiffusiveProcess.CoarseGrainingVocab.reciprocalDirichletTraceLower hd U
      (fun x => s * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m ω x) hc hcInv
    have hmat : aMatrix U hc.toCoeffOn = s • randomAMatrix M m U ω := by
      simpa [hc, hω, randomAMatrix] using aMatrix_const_mul hω hs
    have hmatInv : aMatrix U hcInv.toCoeffOn =
        s • randomAMatrix M m U (T ω) := by
      have hae : Ch02.CoeffOn.AEEq hcInv.toCoeffOn hcT.toCoeffOn :=
        Filter.Eventually.of_forall fun x => by
          have hx := congrFun hfun x
          ext i j
          change scalarMatrix ((s * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m ω x)⁻¹) i j =
            scalarMatrix (s * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m (T ω) x) i j
          rw [hx]
      calc
        aMatrix U hcInv.toCoeffOn = aMatrix U hcT.toCoeffOn :=
          Ch02.aCoarse_eq_ofAEEq hae
        _ = s • randomAMatrix M m U (T ω) := by
          simpa [hcT, hTω, randomAMatrix] using aMatrix_const_mul hTω hs
    rw [hmat, hmatInv, Matrix.trace_smul, Matrix.trace_smul] at htrace
    simpa [smul_eq_mul, mul_add] using htrace
  let traceA : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ :=
    fun ω => Matrix.trace (randomAMatrix M m U ω)
  have htraceInt : Integrable traceA M.P.toMeasure :=
    integrable_trace_randomAMatrix M m U
  have hTpres : MeasurePreserving T M.P.toMeasure M.P.toMeasure :=
    ⟨measurable_negatePotentialSequence, potentialSequenceLaw_negation M⟩
  have htraceTInt : Integrable (traceA ∘ T) M.P.toMeasure :=
    hTpres.integrable_comp_of_integrable htraceInt
  have hrhsInt : Integrable
      (fun ω => s * (traceA ω + traceA (T ω))) M.P.toMeasure :=
    (htraceInt.add htraceTInt).const_mul s
  have hconstInt : Integrable
      (fun _ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => 2 * (d : ℝ))
      M.P.toMeasure := integrable_const _
  have hint := integral_mono hconstInt hrhsInt hpath
  have hTIntegral :
      ∫ ω, traceA (T ω) ∂M.P.toMeasure = ∫ ω, traceA ω ∂M.P.toMeasure :=
    Homogenization.integral_comp_eq_of_map_eq measurable_negatePotentialSequence
      (potentialSequenceLaw_negation M) traceA htraceInt.aestronglyMeasurable
  have htraceAbar :
      ∫ ω, traceA ω ∂M.P.toMeasure = Matrix.trace (abar M m U) := by
    unfold traceA Matrix.trace abar
    rw [integral_finset_sum Finset.univ]
    · apply Finset.sum_congr rfl
      intro i _hi
      simpa [Matrix.diag] using
        (Homogenization.integral_matrix_apply (integrable_randomAMatrix M m U) i i).symm
    · intro i _hi
      exact ((integrable_randomAMatrix M m U).eval i).eval i
  have hmassReal : M.P.toMeasure.real Set.univ = 1 := by
    simp [MeasureTheory.measureReal_def]
  have hsumIntegral :
      ∫ ω, traceA ω + traceA (T ω) ∂M.P.toMeasure =
        (∫ ω, traceA ω ∂M.P.toMeasure) + ∫ ω, traceA (T ω) ∂M.P.toMeasure := by
    simpa only [Function.comp_apply] using integral_add htraceInt htraceTInt
  rw [integral_const, hmassReal, one_smul, integral_const_mul,
    hsumIntegral, hTIntegral, htraceAbar] at hint
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd)
  have hsEq : s = Real.exp ((m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := rfl
  rw [abarScalarReadout]
  change Real.exp (-(m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤
    Matrix.trace (abar M m U) / (d : ℝ)
  rw [hsEq] at hint
  have hexpInv :
      Real.exp (-(m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
        (Real.exp ((m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))⁻¹ := by
    rw [show -(m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P =
      -((m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) by ring, Real.exp_neg]
  rw [hexpInv]
  have hexpPos := Real.exp_pos ((m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
  apply (le_div_iff₀ hdpos).2
  apply (inv_mul_le_iff₀ hexpPos).2
  nlinarith

/-- Provider export with the exact type of the frozen Section 5 anchor. -/
theorem homogenized_coefficient_reciprocal_lower {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) :
    Real.exp (-(m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤ ahom M m := by
  exact ge_of_tendsto (tendsto_abarScalarReadout_ahom M m)
    (Filter.Eventually.of_forall fun n => finiteVolume_reciprocal_lower M m n)

end

end SubdiffusiveProcess.Providers.Section5
